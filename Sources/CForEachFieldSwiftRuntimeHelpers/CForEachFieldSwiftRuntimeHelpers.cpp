#include "CForEachFieldSwiftRuntimeHelpers.h"

#include <atomic>
#include <cassert>
#include <cstdlib>
#include <cstdio>
#include <cinttypes>
#include <cstring>
#include <tuple>
#include <type_traits>
#include <utility>

#if __APPLE__
#include <objc/objc.h>
#include <objc/runtime.h>
#include <objc/objc-api.h>
#endif

[[noreturn]] static void fatalError(const char *message) {
    fprintf(stderr, "%s\n", message);
    std::abort();
}

static size_t classIsSwiftMask() {
#if __APPLE__
    if (__builtin_available(macOS 10.14.4, iOS 12.2, tvOS 12.2, watchOS 5.2, *)) {
        return 2;
    }
#endif
    return 1;
}

static std::pair<const char*, size_t> makeSymbolicMangledName(const char *base) {
    if (!base)
        return {nullptr, 0};

    const char *end = base;
    while (*end != '\0') {
        // Skip over symbolic references.
        if (*end >= '\x01' && *end <= '\x17')
            end += sizeof(uint32_t);
        else if (*end >= '\x18' && *end <= '\x1F')
            end += sizeof(void*);
        ++end;
    }
    return {base, end - base};
}

// MARK: - RelativePointer
// See https://github.com/apple/swift/blob/aa3e5904f8ba8bf9ae06d96946774d171074f6e5/include/swift/Basic/RelativePointer.h
namespace {

namespace relative_pointer_helpers {

/// Apply a relative offset to a base pointer. The offset is applied to the base
/// pointer using sign-extended, wrapping arithmetic.
template<typename BasePtrTy, typename Offset>
static inline uintptr_t applyRelativeOffset(BasePtrTy *basePtr, Offset offset) {
    static_assert(std::is_integral<Offset>::value &&
                  std::is_signed<Offset>::value,
                  "offset type should be signed integer");

    auto base = reinterpret_cast<uintptr_t>(basePtr);
    // We want to do wrapping arithmetic, but with a sign-extended
    // offset. To do this in C, we need to do signed promotion to get
    // the sign extension, but we need to perform arithmetic on unsigned values,
    // since signed overflow is undefined behavior.
    auto extendOffset = (uintptr_t)(intptr_t)offset;
    return base + extendOffset;
}

/// Measure the relative offset between two pointers. This measures
/// (referent - base) using wrapping arithmetic. The result is truncated if
/// Offset is smaller than a pointer, with an assertion that the
/// pre-truncation result is a sign extension of the truncated result.
template<typename Offset, typename A, typename B>
static inline Offset measureRelativeOffset(A *referent, B *base) {
    static_assert(std::is_integral<Offset>::value &&
                  std::is_signed<Offset>::value,
                  "offset type should be signed integer");

    auto distance = (uintptr_t)referent - (uintptr_t)base;
    // Truncate as unsigned, then wrap around to signed.
    auto truncatedDistance =
    (Offset)(typename std::make_unsigned<Offset>::type)distance;
    // Assert that the truncation didn't discard any non-sign-extended bits.
    assert((intptr_t)truncatedDistance == (intptr_t)distance
           && "pointers are too far apart to fit in offset type");
    return truncatedDistance;
}

} // namespace relative_pointer_helpers

/// A relative reference to an object stored in memory. The reference may be
/// direct or indirect, and uses the low bit of the (assumed at least
/// 2-byte-aligned) pointer to differentiate.
template<typename ValueTy,
         bool Nullable = false,
         typename Offset = int32_t,
         typename IndirectType = const ValueTy *>
class RelativeIndirectablePointer {
private:
    static_assert(std::is_integral<Offset>::value &&
                  std::is_signed<Offset>::value,
                  "offset type should be signed integer");

    /// The relative offset of the pointer's memory from the `this` pointer.
    /// If the low bit is clear, this is a direct reference; otherwise, it is
    /// an indirect reference.
    Offset relativeOffsetPlusIndirect;

    /// RelativePointers should appear in statically-generated metadata. They
    /// shouldn't be constructed or copied.
    RelativeIndirectablePointer() = delete;
    RelativeIndirectablePointer(RelativeIndirectablePointer &&) = delete;
    RelativeIndirectablePointer(const RelativeIndirectablePointer &) = delete;
    RelativeIndirectablePointer &operator=(RelativeIndirectablePointer &&) = delete;
    RelativeIndirectablePointer &operator=(const RelativeIndirectablePointer &) = delete;

public:
    // TODO: Dead code?
    /// Allow construction and reassignment from an absolute pointer.
    /// These always produce a direct relative offset.
    RelativeIndirectablePointer(ValueTy *absolute)
        : relativeOffsetPlusIndirect(
              Nullable && absolute == nullptr
                  ? 0
                  : relative_pointer_helpers::measureRelativeOffset<Offset>(absolute,
                                                                            this)
          ) {
        if (!Nullable) {
            assert(absolute != nullptr &&
                   "constructing non-nullable relative pointer from null");
        }
    }

    // TODO: Dead code?
    RelativeIndirectablePointer &operator=(ValueTy *absolute) & {
        if (!Nullable) {
            assert(absolute != nullptr &&
                   "constructing non-nullable relative pointer from null");
        }

        relativeOffsetPlusIndirect = Nullable && absolute == nullptr
            ? 0
            : relative_pointer_helpers::measureRelativeOffset<Offset>(absolute, this);
        return *this;
    }

    const ValueTy *get() const & {
        static_assert(alignof(ValueTy) >= 2 && alignof(Offset) >= 2,
                      "alignment of value and offset must be at least 2 to "
                      "make room for indirectable flag");

        // Check for null.
        if (Nullable && relativeOffsetPlusIndirect == 0)
            return nullptr;

        Offset offsetPlusIndirect = relativeOffsetPlusIndirect;
        uintptr_t address = relative_pointer_helpers::applyRelativeOffset(this,
                                                        offsetPlusIndirect & ~1);

        // If the low bit is set, then this is an indirect address. Otherwise,
        // it's direct.
        if (offsetPlusIndirect & 1) {
            return *reinterpret_cast<IndirectType const *>(address);
        } else {
            return reinterpret_cast<const ValueTy *>(address);
        }
    }

    /// A zero relative offset encodes a null reference.
    bool isNull() const & {
        return relativeOffsetPlusIndirect == 0;
    }

    operator const ValueTy* () const & {
        return get();
    }

    const ValueTy *operator->() const & {
        return get();
    }
};

/// A relative reference to a function, intended to reference private metadata
/// functions for the current executable or dynamic library image from
/// position-independent constant data.
template<typename T, bool Nullable, typename Offset>
class RelativeDirectPointerImpl {
private:
    /// The relative offset of the function's entry point from *this.
    Offset relativeOffset;

    /// RelativePointers should appear in statically-generated metadata. They
    /// shouldn't be constructed or copied.
    RelativeDirectPointerImpl() = delete;
    /// RelativePointers should appear in statically-generated metadata. They
    /// shouldn't be constructed or copied.
    RelativeDirectPointerImpl(RelativeDirectPointerImpl &&) = delete;
    RelativeDirectPointerImpl(const RelativeDirectPointerImpl &) = delete;
    RelativeDirectPointerImpl &operator=(RelativeDirectPointerImpl &&) = delete;
    RelativeDirectPointerImpl &operator=(const RelativeDirectPointerImpl &) = delete;

public:
    using ValueTy = T;
    using PointerTy = T*;

    // Allow construction and reassignment from an absolute pointer.
    RelativeDirectPointerImpl(PointerTy absolute)
        : relativeOffset(
            Nullable && absolute == nullptr
                ? 0
                : relative_pointer_helpers::measureRelativeOffset<Offset>(absolute,
                                                                          this)
          )
    {
        if (!Nullable) {
            assert(absolute != nullptr &&
                   "constructing non-nullable relative pointer from null");
        }
    }

    explicit constexpr RelativeDirectPointerImpl(std::nullptr_t)
        : relativeOffset (0)
    {
        static_assert(Nullable, "can't construct non-nullable pointer from null");
    }

    RelativeDirectPointerImpl &operator=(PointerTy absolute) & {
        if (!Nullable) {
            assert(absolute != nullptr &&
                   "constructing non-nullable relative pointer from null");
        }
        relativeOffset = Nullable && absolute == nullptr
            ? 0
            : relative_pointer_helpers::measureRelativeOffset<Offset>(absolute, this);
        return *this;
    }

    PointerTy get() const & {
        // Check for null.
        if (Nullable && relativeOffset == 0)
            return nullptr;

        // The value is addressed relative to `this`.
        uintptr_t absolute =
            relative_pointer_helpers::applyRelativeOffset(this, relativeOffset);
        return reinterpret_cast<PointerTy>(absolute);
    }

    /// A zero relative offset encodes a null reference.
    bool isNull() const & {
        return relativeOffset == 0;
    }
};

template <typename T, bool Nullable = true, typename Offset = int32_t,
          typename = void>
class RelativeDirectPointer;

/// A direct relative reference to an object that is not a function pointer.
template <typename T, bool Nullable, typename Offset>
class RelativeDirectPointer<T,
                            Nullable,
                            Offset,
                            typename std::enable_if<!std::is_function<T>::value>::type>
    : private RelativeDirectPointerImpl<T, Nullable, Offset>
{
    using super = RelativeDirectPointerImpl<T, Nullable, Offset>;
public:
    using super::get;
    using super::super;

    RelativeDirectPointer &operator=(T *absolute) & {
        super::operator=(absolute);
        return *this;
    }

    operator typename super::PointerTy() const & {
        return this->get();
    }

    const typename super::ValueTy *operator->() const & {
        return this->get();
    }

    using super::isNull;
};

/// A specialization of RelativeDirectPointer for function pointers,
/// allowing for calls.
template<typename T, bool Nullable, typename Offset>
class RelativeDirectPointer<T,
                            Nullable,
                            Offset,
                            typename std::enable_if<std::is_function<T>::value>::type>
    : private RelativeDirectPointerImpl<T, Nullable, Offset>
{
    using super = RelativeDirectPointerImpl<T, Nullable, Offset>;
public:
    using super::super;

    RelativeDirectPointer &operator=(T absolute) & {
        super::operator=(absolute);
        return *this;
    }

    typename super::PointerTy get() const & {
        auto ptr = this->super::get();
#if SWIFT_PTRAUTH
        if (Nullable && !ptr)
            return ptr;
        return ptrauth_sign_unauthenticated(ptr, ptrauth_key_function_pointer, 0);
#else
        return ptr;
#endif
    }

    operator typename super::PointerTy() const & {
        return this->get();
    }

    template <typename...ArgTy>
    typename std::result_of<T* (ArgTy...)>::type operator()(ArgTy...arg) const {
#if SWIFT_PTRAUTH
        return ptrauth_sign_unauthenticated(this->super::get(),
                                            ptrauth_key_function_pointer,
                                            0)(std::forward<ArgTy>(arg)...);
#else
        return this->super::get()(std::forward<ArgTy>(arg)...);
#endif
    }

    using super::isNull;
};

} // end anonymous namespace

// MARK: - MetadataKind

// The values used here are taken from
// https://github.com/apple/swift/blob/424802fb34a7d47d0d507cd71b10200ecf5eaff1/include/swift/ABI/MetadataValues.h#L51-L83
namespace {

const unsigned MetadataKindIsNonType = 0x400;

const unsigned MetadataKindIsNonHeap = 0x200;

const unsigned MetadataKindIsRuntimePrivate = 0x100;

enum class MetadataKind : uint32_t {

    /// A class type.
    Class = 0,

    /// A struct type.
    Struct = 0 | MetadataKindIsNonHeap,

    /// An enum type.
    Enum = 1 | MetadataKindIsNonHeap,

    /// An optional type.
    Optional = 2 | MetadataKindIsNonHeap,

    /// A foreign class, such as a Core Foundation class.
    ForeignClass = 3 | MetadataKindIsNonHeap,

    /// A type whose value is not exposed in the metadata system.
    Opaque = 0 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// A tuple.
    Tuple = 1 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// A monomorphic function.
    Function = 2 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// An existential type.
    Existential = 3 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// A metatype.
    Metatype = 4 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// An ObjC class wrapper.
    ObjCClassWrapper = 5 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// An existential metatype.
    ExistentialMetatype = 6 | MetadataKindIsRuntimePrivate | MetadataKindIsNonHeap,

    /// A heap-allocated local variable using statically-generated metadata.
    HeapLocalVariable = 0 | MetadataKindIsNonType,

    /// A heap-allocated local variable using runtime-instantiated metadata.
    HeapGenericLocalVariable = 0 | MetadataKindIsNonType | MetadataKindIsRuntimePrivate,

    /// A native error object.
    ErrorObject = 1 | MetadataKindIsNonType | MetadataKindIsRuntimePrivate,

    /// A heap-allocated simple task.
    SimpleTask = 2 | MetadataKindIsNonType | MetadataKindIsRuntimePrivate,

    /// The largest possible non-isa-pointer metadata kind value.
    LastEnumerated = 0x7FF,
};

} // end anonymous namespace

// MARK: - Metadata

namespace {

class TypeContextDescriptor;
class ClassDescriptor;

// Field records describe the type of a single stored property or case member
// of a class, struct or enum.
class FieldRecordFlags {
    using int_type = uint32_t;
    enum : int_type {
        // Is this an indirect enum case?
        IsIndirectCase = 0x1,

        // Is this a mutable `var` property?
        IsVar = 0x2,
    };
    int_type data = 0;

public:
    bool isIndirectCase() const {
        return (data & IsIndirectCase) == IsIndirectCase;
    }

    bool isVar() const {
        return (data & IsVar) == IsVar;
    }

    void setIsIndirectCase(bool IndirectCase = true) {
        if (IndirectCase)
            data |= IsIndirectCase;
        else
            data &= ~IsIndirectCase;
    }

    void setIsVar(bool Var = true) {
        if (Var)
            data |= IsVar;
        else
            data &= ~IsVar;
    }

    int_type getRawValue() const {
        return data;
    }
};

class FieldRecord {
    const FieldRecordFlags flags;

public:
    const RelativeDirectPointer<const char> mangledTypeName;
    const RelativeDirectPointer<const char> fieldName;

    FieldRecord() = delete;

    bool hasMangledTypeName() const {
        return mangledTypeName;
    }

    std::pair<const char*, size_t> getMangledTypeName() const {
        return makeSymbolicMangledName(mangledTypeName.get());
    }

    const char *getFieldName() const {
        return fieldName;
    }

    bool isIndirectCase() const {
        return flags.isIndirectCase();
    }
};

class FieldDescriptor {
    RelativeDirectPointer<const char> mangledTypeName;
    RelativeDirectPointer<const char> superclass;

    uint16_t kind;
    uint16_t fieldRecordSize;
    uint32_t numFields;

public:
    const FieldRecord *getFieldRecordBuffer() const {
        return reinterpret_cast<const FieldRecord *>(this + 1);
    }
};

struct Metadata {
    MetadataKind getKind() const {
        if (kind > uintptr_t(MetadataKind::LastEnumerated)) {
            return MetadataKind::Class;
        }
        return MetadataKind(kind);
    }

    /// Get the nominal type descriptor if this metadata describes a nominal type,
    /// or return null if it does not.
    const TypeContextDescriptor *getTypeContextDescriptor() const;

    /// Retrieve the generic arguments of this type, if it has any.
    const Metadata *const *getGenericArgs() const;
private:
    uintptr_t kind;
};

struct TupleTypeMetadata : Metadata {
    size_t numElements;
    const char *labels;

    struct Element {
        /// The type of the element.
        const Metadata *type;

        /// The offset of the tuple element within the tuple.
#if __APPLE__
        size_t offset;
#else
        uint32_t offset;
#endif
    };

    static_assert(sizeof(Element) == sizeof(size_t) * 2,
                  "element size should be two words");

    const Element *getElements() const {
        return reinterpret_cast<const Element*>(this + 1);
    }

    const Element &getElement(size_t i) const {
        return getElements()[i];
    }
};

/// The common structure of all metadata for heap-allocated types.  A
/// pointer to one of these can be retrieved by loading the 'isa'
/// field of any heap object, whether it was managed by Swift or by
/// Objective-C.  However, when loading from an Objective-C object,
/// this metadata may not have the heap-metadata header, and it may
/// not be the Swift type metadata for the object's dynamic type.
struct HeapMetadata : Metadata {};

struct ClassMetadata;

/// The portion of a class metadata object that is compatible with
/// all classes, even non-Swift ones.
struct AnyClassMetadata : HeapMetadata {

    /// The metadata for the superclass.  This is null for the root class.
    const ClassMetadata *superclass;

#if __APPLE__
    /// The cache data is used for certain dynamic lookups; it is owned
    /// by the runtime and generally needs to interoperate with
    /// Objective-C's use.
    void *cacheData[2];

    /// The data pointer is used for out-of-line metadata and is
    /// generally opaque, except that the compiler sets the low bit in
    /// order to indicate that this is a Swift metatype and therefore
    /// that the type metadata header is present.
    size_t data;
#endif

    /// Is this object a valid swift type metadata?  That is, can it be
    /// safely downcast to ClassMetadata?
    bool isTypeMetadata() const {
#if __APPLE__
        return data & classIsSwiftMask();
#else
        return true;
#endif
    }
};

/// Swift class flags.
/// These flags are valid only when isTypeMetadata().
/// When !isTypeMetadata() these flags will collide with other Swift ABIs.
enum class ClassFlags : uint32_t {
    /// Is this a Swift class from the Darwin pre-stable ABI?
    /// This bit is clear in stable ABI Swift classes.
    /// The Objective-C runtime also reads this bit.
    IsSwiftPreStableABI = 0x1,

    /// Does this class use Swift refcounting?
    UsesSwiftRefcounting = 0x2,

    /// Has this class a custom name, specified with the @objc attribute?
    HasCustomObjCName = 0x4,

    /// Whether this metadata is a specialization of a generic metadata pattern
    /// which was created during compilation.
    IsStaticSpecialization = 0x8,

    /// Whether this metadata is a specialization of a generic metadata pattern
    /// which was created during compilation and made to be canonical by
    /// modifying the metadata accessor.
    IsCanonicalStaticSpecialization = 0x10,
};

bool operator&(ClassFlags a, ClassFlags b) {
    return (uint32_t(a) & uint32_t(b)) != 0;
}

struct ClassMetadata : AnyClassMetadata {

    /// Swift-specific class flags.
    ClassFlags flags;

    /// The address point of instances of this type.
    uint32_t instanceAddressPoint;

    /// The required size of instances of this type.
    /// 'InstanceAddressPoint' bytes go before the address point;
    /// 'InstanceSize - InstanceAddressPoint' bytes go after it.
    uint32_t instanceSize;

    /// The alignment mask of the address point of instances of this type.
    uint16_t instanceAlignMask;

    /// Reserved for runtime use.
    uint16_t reserved;

    /// The total size of the class object, including prefix and suffix
    /// extents.
    uint32_t classSize;

    /// The offset of the address point within the class object.
    uint32_t classAddressPoint;

    // Description is by far the most likely field for a client to try
    // to access directly, so we force access to go through accessors.
private:
    /// An out-of-line Swift-specific description of the type, or null
    /// if this is an artificial subclass.  We currently provide no
    /// supported mechanism for making a non-artificial subclass
    /// dynamically.
    const ClassDescriptor *description;

public:
    /// A function for destroying instance variables, used to clean up after an
    /// early return from a constructor. If null, no clean up will be performed
    /// and all ivars must be trivial.
    void *ivarDestroyer;

    /// Is this class an artificial subclass, such as one dynamically
    /// created for various dynamic purposes like KVO?
    bool isArtificialSubclass() const {
        assert(isTypeMetadata());
        return description == nullptr;
    }

    const ClassDescriptor *getDescription() const {
        assert(isTypeMetadata());
        return description;
    }

    ClassFlags getFlags() const {
        assert(isTypeMetadata());
        return flags;
    }

    /// Get a pointer to the field offset vector, if present, or null.
    const uintptr_t *getFieldOffsets() const;
};

/// The structure of metadata for foreign types where the source
/// language doesn't provide any sort of more interesting metadata for
/// us to use.
struct ForeignTypeMetadata : Metadata {};

/// The structure of metadata objects for foreign class types.
/// A foreign class is a foreign type with reference semantics and
/// Swift-supported reference counting.  Generally this requires
/// special logic in the importer.
///
/// We assume for now that foreign classes are entirely opaque
/// to Swift introspection.
struct ForeignClassMetadata : ForeignTypeMetadata {
    /// An out-of-line description of the type.
    const ClassDescriptor *description;

    /// The superclass of the foreign class, if any.
    const ForeignClassMetadata *superclass;

    /// Reserved space. For now, this should be zero-initialized.
    /// If this is used for anything in the future, at least some of these
    /// first bits should be flags.
    void* Reserved[1];
};

/// Kinds of context descriptor.
enum class ContextDescriptorKind : uint8_t {
    /// This context descriptor represents a module.
    Module = 0,

    /// This context descriptor represents an extension.
    Extension = 1,

    /// This context descriptor represents an anonymous possibly-generic context
    /// such as a function body.
    Anonymous = 2,

    /// This context descriptor represents a protocol context.
    Protocol = 3,

    /// This context descriptor represents an opaque type alias.
    OpaqueType = 4,

    /// First kind that represents a type of any sort.
    Type_First = 16,

    /// This context descriptor represents a class.
    Class = Type_First,

    /// This context descriptor represents a struct.
    Struct = Type_First + 1,

    /// This context descriptor represents an enum.
    Enum = Type_First + 2,

    /// Last kind that represents a type of any sort.
    Type_Last = 31,
};

/// Common flags stored in the first 32-bit word of any context descriptor.
struct ContextDescriptorFlags {
    /// The kind of context this descriptor describes.
    constexpr ContextDescriptorKind getKind() const {
        return ContextDescriptorKind(value & 0x1Fu);
    }

    /// The most significant two bytes of the flags word, which can have
    /// kind-specific meaning.
    constexpr uint16_t getKindSpecificFlags() const {
        return (value >> 16u) & 0xFFFFu;
    }
private:
    uint32_t value;
};

struct GenericContext {
    // TODO
};

/// Base class for all context descriptors.
struct ContextDescriptor {
    ContextDescriptorFlags flags;

    /// The parent context, or null if this is a top-level context.
    RelativeIndirectablePointer<const ContextDescriptor,
                                /*nullable*/true,
                                int32_t> parent;

    ContextDescriptorKind getKind() const { return flags.getKind(); }

    /// Get the generic context information for this context, or null if the
    /// context is not generic.
    const GenericContext *getGenericContext() const {
        // TODO
        return nullptr;
    }
};

class TypeContextDescriptorFlags {
    uint16_t value;
public:
    TypeContextDescriptorFlags(uint16_t v) : value(v) {}

    bool class_areImmediateMembersNegative() {
        return value & (1 << 12);
    }

    bool class_hasResilientSuperclass() {
        return value & (1 << 13);
    }
};

class TypeContextDescriptor : public ContextDescriptor {
public:
    /// The name of the type.
    RelativeDirectPointer<const char, /*nullable*/false> name;

    /// A pointer to the metadata access function for this type.
    ///
    /// The function type here is a stand-in. You should use getAccessFunction()
    /// to wrap the function pointer in an accessor that uses the proper calling
    /// convention for a given number of arguments.
    int32_t accessFunctionPtr;

    /// A pointer to the field descriptor for the type, if any.
    RelativeDirectPointer<const FieldDescriptor, /*nullable*/ true> fields;

    bool isReflectable() const { return bool(fields); }

    /// Return the offset of the start of generic arguments in the nominal
    /// type's metadata. The returned value is measured in sizeof(sizt_t).
    int32_t getGenericArgumentOffset() const;

    TypeContextDescriptorFlags getTypeContextDescriptorFlags() const {
        return TypeContextDescriptorFlags(flags.getKindSpecificFlags());
    }
};

class ValueTypeDescriptor : public TypeContextDescriptor {};

class StructDescriptor : public ValueTypeDescriptor {
public:
    /// The number of stored properties in the struct.
    /// If there is a field offset vector, this is its length.
    uint32_t numFields;
    /// The offset of the field offset vector for this struct's stored
    /// properties in its metadata, if any. 0 means there is no field offset
    /// vector.
    uint32_t fieldOffsetVectorOffset;
};

class EnumDescriptor : public ValueTypeDescriptor {
public:
    /// The number of non-empty cases in the enum are in the low 24 bits;
    /// the offset of the payload size in the metadata record in words,
    /// if any, is stored in the high 8 bits.
    uint32_t NumPayloadCasesAndPayloadSizeOffset;

    /// The number of empty cases in the enum.
    uint32_t NumEmptyCases;
};

struct MetadataBounds {
    /// The negative extent of the metadata, in words.
    uint32_t negativeSizeInWords;

    /// The positive extent of the metadata, in words.
    uint32_t positiveSizeInWords;
};

struct ClassMetadataBounds : MetadataBounds {
    /// The offset from the address point of the metadata to the immediate
    /// members.
    ptrdiff_t immediateMembersOffset;

    ClassMetadataBounds() : MetadataBounds{0, 0}, immediateMembersOffset(0) {}

    constexpr ClassMetadataBounds(ptrdiff_t immediateMembersOffset,
                                  uint32_t negativeSizeInWords,
                                  uint32_t positiveSizeInWords)
        : MetadataBounds{negativeSizeInWords, positiveSizeInWords},
          immediateMembersOffset(immediateMembersOffset)
    {}
};

ClassMetadataBounds getResilientMetadataBounds(const ClassDescriptor *description);

class StoredClassMetadataBounds {
    /// The offset to the immediate members.  This value is in bytes so that
    /// clients don't have to sign-extend it.
    /// It is not necessary to use atomic-ordered loads when accessing this
    /// variable just to read the immediate-members offset when drilling to
    /// the immediate members of an already-allocated metadata object.
    /// The proper initialization of this variable is always ordered before
    /// any allocation of metadata for this class.
    std::atomic<ptrdiff_t> immediateMembersOffset;

    /// The positive and negative bounds of the class metadata.
    MetadataBounds bounds;

public:
    /// Attempt to read the full cached bounds.
    ///
    /// \return true if the read was successful, or false if the cache hasn't
    ///   been filled yet
    bool tryGet(ClassMetadataBounds &output) {
        auto offset = immediateMembersOffset.load(std::memory_order_acquire);
        if (offset == 0) return false;

        output.immediateMembersOffset = offset;
        output.negativeSizeInWords = bounds.negativeSizeInWords;
        output.positiveSizeInWords = bounds.positiveSizeInWords;
        return true;
    }
};

class ClassDescriptor : public TypeContextDescriptor {
public:
    /// The type of the superclass, expressed as a mangled type name that can
    /// refer to the generic arguments of the subclass type.
    RelativeDirectPointer<const char> superclassType;

    union {
        /// If this descriptor does not have a resilient superclass, this is the
        /// negative size of metadata objects of this class (in words).
        uint32_t metadataNegativeSizeInWords;

        /// If this descriptor has a resilient superclass, this is a reference
        /// to a cache holding the metadata's extents.
        RelativeDirectPointer<StoredClassMetadataBounds> resilientMetadataBounds;
    };

    union {
        /// If this descriptor does not have a resilient superclass, this is the
        /// positive size of metadata objects of this class (in words).
        uint32_t metadataPositiveSizeInWords;

        /// Otherwise, these flags are used to do things like indicating
        /// the presence of an Objective-C resilient class stub.
        uint32_t extraClassFlags;
    };

    /// The number of additional members added by this class to the class
    /// metadata.  This data is opaque by default to the runtime, other than
    /// as exposed in other members; it's really just
    /// NumImmediateMembers * sizeof(void*) bytes of data.
    ///
    /// Whether those bytes are added before or after the address point
    /// depends on areImmediateMembersNegative().
    uint32_t numImmediateMembers;

    /// The number of stored properties in the class, not including its
    /// superclasses. If there is a field offset vector, this is its length.
    uint32_t numFields;

private:
    /// The offset of the field offset vector for this class's stored
    /// properties in its metadata, in words. 0 means there is no field offset
    /// vector.
    ///
    /// If this class has a resilient superclass, this offset is relative to
    /// the size of the resilient superclass metadata. Otherwise, it is
    /// absolute.
    uint32_t fieldOffsetVectorOffset;

public:

    /// Are the immediate members of the class metadata allocated at negative
    /// offsets instead of positive?
    bool areImmediateMembersNegative() const {
        return getTypeContextDescriptorFlags().class_areImmediateMembersNegative();
    }

    /// Given that this class is known to not have a resilient superclass
    /// return its metadata bounds.
    ClassMetadataBounds getNonResilientMetadataBounds() const {
        return {
            ptrdiff_t(getNonResilientImmediateMembersOffset() * sizeof(void*)),
            metadataNegativeSizeInWords,
            metadataPositiveSizeInWords
        };
    }

    bool hasResilientSuperclass() const {
        return getTypeContextDescriptorFlags().class_hasResilientSuperclass();
    }

    /// Given that this class is known to not have a resilient superclass,
    /// return the offset of its immediate members in words.
    int32_t getNonResilientImmediateMembersOffset() const {
        assert(!hasResilientSuperclass());
        return areImmediateMembersNegative()
        ? -int32_t(metadataNegativeSizeInWords)
        : int32_t(metadataPositiveSizeInWords - numImmediateMembers);
    }

    /// Return the bounds of this class's metadata.
    ClassMetadataBounds getMetadataBounds() const {
        if (!hasResilientSuperclass()) {
            return getNonResilientMetadataBounds();
        }

        return getResilientMetadataBounds(this);
    }

    uint32_t getFieldOffsetVectorOffset() const {
        if (hasResilientSuperclass()) {
            ClassMetadataBounds bounds = getMetadataBounds();
            return uint32_t(bounds.immediateMembersOffset / sizeof(uintptr_t) +
                            fieldOffsetVectorOffset);
        }

        return fieldOffsetVectorOffset;
    }
};

/// Decide dynamically whether the given class uses native Swift
/// reference-counting.
bool usesNativeSwiftReferenceCounting(const ClassMetadata *theClass) {
#if __APPLE__
    if (!theClass->isTypeMetadata()) {
        return false;
    }
    return (theClass->getFlags() & ClassFlags::UsesSwiftRefcounting);
#else
    return true;
#endif
}

struct ValueMetadata : Metadata {
    const ValueTypeDescriptor *description;
};

struct StructMetadata : ValueMetadata {

    const StructDescriptor *getDescription() const {
        return static_cast<const StructDescriptor*>(this->description);
    }

    /// Get a pointer to the field offset vector, if present, or null.
    const uint32_t *getFieldOffsets() const {
        uint32_t offset = getDescription()->fieldOffsetVectorOffset;
        if (offset == 0)
            return nullptr;
        auto asWords = reinterpret_cast<const void * const*>(this);
        return reinterpret_cast<const uint32_t *>(asWords + offset);
    }
};

const TypeContextDescriptor *Metadata::getTypeContextDescriptor() const {
    switch (getKind()) {
        case MetadataKind::Class: {
            const auto *cls = static_cast<const ClassMetadata*>(this);
            if (!cls->isTypeMetadata()) {
                return nullptr;
            }
            if (cls->isArtificialSubclass()) {
                return nullptr;
            }
            return cls->getDescription();
        }
        case MetadataKind::Struct:
        case MetadataKind::Enum:
        case MetadataKind::Optional:
            return static_cast<const ValueMetadata *>(this)->description;
        case MetadataKind::ForeignClass:
            return static_cast<const ForeignClassMetadata *>(this)->description;
        default:
            return nullptr;
    }
}

const Metadata *const *Metadata::getGenericArgs() const {
    const TypeContextDescriptor *description = getTypeContextDescriptor();
    if (!description)
        return nullptr;

    auto generics = description->getGenericContext();
    if (!generics)
        return nullptr;

    auto asWords = reinterpret_cast<const Metadata *const *>(this);
    return asWords + description->getGenericArgumentOffset();
}

const uintptr_t *ClassMetadata::getFieldOffsets() const {
    assert(isTypeMetadata());
    auto offset = getDescription()->getFieldOffsetVectorOffset();
    if (offset == 0) {
        return nullptr;
    }
    auto asWords = reinterpret_cast<const void * const*>(this);
    return reinterpret_cast<const uintptr_t *>(asWords + offset);
}

int32_t TypeContextDescriptor::getGenericArgumentOffset() const {
  switch (getKind()) {
  case ContextDescriptorKind::Class:
    return static_cast<const ClassDescriptor*>(this)->getGenericArgumentOffset();
  case ContextDescriptorKind::Enum:
    return static_cast<const EnumDescriptor*>(this)->getGenericArgumentOffset();
  case ContextDescriptorKind::Struct:
    return static_cast<const StructDescriptor*>(this)->getGenericArgumentOffset();
  default:
    fatalError("Not a type context descriptor.");
  }
}

static ClassMetadataBounds computeMetadataBoundsFromSuperclass(
   const ClassDescriptor *description,
   StoredClassMetadataBounds &storedBounds
) {
    ClassMetadataBounds bounds;

    // Compute the bounds for the superclass, extending it to the minimum
    // bounds of a Swift class.
    if (const void *superRef = description->getResilientSuperclass()) {
        fatalError("unimplemented");
//        bounds = computeMetadataBoundsForSuperclass(superRef,
//                                                    description->getResilientSuperclassReferenceKind());
    } else {
        bounds = ClassMetadataBounds::forSwiftRootClass();
    }

    // Add the subclass's immediate members.
    bounds.adjustForSubclass(description->areImmediateMembersNegative(),
                             description->numImmediateMembers);

    // Cache before returning.
    storedBounds.initialize(bounds);
    return bounds;
}

ClassMetadataBounds getResilientMetadataBounds(const ClassDescriptor *description) {
    assert(description->hasResilientSuperclass());
    StoredClassMetadataBounds &storedBounds = *description->resilientMetadataBounds.get();

    ClassMetadataBounds bounds;
    if (storedBounds.tryGet(bounds)) {
        return bounds;
    }

    return computeMetadataBoundsFromSuperclass(description, storedBounds);
}

} // end anonymous namespace

// MARK: - ReflectionMirror
namespace {

namespace reflection_mirror {

class FieldType {
    const Metadata *type;
    bool indirect;
    uint8_t referenceOwnership;
public:

    constexpr FieldType() : type(nullptr), indirect(false), referenceOwnership(0) {}

    constexpr FieldType(const Metadata *T)
        : type(T), indirect(false), referenceOwnership(0)
    {}

    static constexpr FieldType untypedEnumCase(bool indirect) {
        FieldType type{};
        type.indirect = indirect;
        return type;
    }
    const Metadata *getType() const { return type; }
    bool isIndirect() const { return indirect; }
    void setIndirect(bool value) { indirect = value; }

    const uint8_t getReferenceOwnership() const { return referenceOwnership; }

    void setReferenceOwnership(uint8_t newOwnership) {
        referenceOwnership = newOwnership;
    }
};

__attribute__((swiftcall))
extern "C"
const Metadata *
swift_getTypeByMangledNameInContext(const char *typeNameStart,
                                    size_t typeNameLength,
                                    const ContextDescriptor *context,
                                    const Metadata * const *genericArgs);

static std::pair<const char* /*name*/, FieldType /*fieldInfo*/>
getFieldAt(const Metadata *base, size_t index) {
    // If we failed to find the field descriptor metadata for the type, fall
    // back to returning an empty tuple as a standin.
//    auto failedToFindMetadata = [&]() -> std::pair<const char*, FieldType> {
//        auto typeName = swift_getTypeName(base, /*qualified*/ true);
//        missing_reflection_metadata_warning(
//                                            "warning: the Swift runtime found no field metadata for "
//                                            "type '%*s' that claims to be reflectable. Its fields will show up as "
//                                            "'unknown' in Mirrors\n",
//                                            (int)typeName.length, typeName.data);
//        return {"unknown", FieldType(&METADATA_SYM(EMPTY_TUPLE_MANGLING))};
//    };

    auto *baseDesc = base->getTypeContextDescriptor();
    if (!baseDesc) {
        fatalError("failed to fined field metadata");
//        return failedToFindMetadata();
    }

    auto *fields = baseDesc->fields.get();
    if (!fields) {
        fatalError("failed to fined field metadata");
//        return failedToFindMetadata();
    }

    auto &field = fields->getFieldRecordBuffer()[index];
    // Bounds are always valid as the offset is constant.
    auto name = field.getFieldName();

    // Enum cases don't always have types.
    if (!field.hasMangledTypeName())
        return {name, FieldType::untypedEnumCase(field.isIndirectCase())};

    std::pair<const char*, size_t> typeName = field.getMangledTypeName();

    const Metadata *metadata =
        swift_getTypeByMangledNameInContext(typeName.first,
                                            typeName.second,
                                            base->getTypeContextDescriptor(),
                                            base->getGenericArgs());
//    SubstGenericParametersFromMetadata substitutions(base);
//    auto result = swift_getTypeByMangledName(MetadataState::Complete, typeName, substitutions.getGenericArgs(),
//                                             [&substitutions](unsigned depth, unsigned index) {
//                                                 return substitutions.getMetadata(depth, index);
//                                             },
//                                             [&substitutions](const Metadata *type, unsigned index) {
//                                                 return substitutions.getWitnessTable(type, index);
//                                             });
//
//    // If demangling the type failed, pretend it's an empty type instead with
//    // a log message.
//    TypeInfo typeInfo;
//    if (result.isError()) {
////        typeInfo = TypeInfo({&METADATA_SYM(EMPTY_TUPLE_MANGLING),
////            MetadataState::Complete}, {});
////
////        auto *error = result.getError();
////        char *str = error->copyErrorString();
////        missing_reflection_metadata_warning(
////                                            "warning: the Swift runtime was unable to demangle the type "
////                                            "of field '%*s'. the mangled type name is '%*s': %s. this field will "
////                                            "show up as an empty tuple in Mirrors\n",
////                                            (int)name.size(), name.data(), (int)typeName.size(), typeName.data(),
////                                            str);
////        error->freeErrorString(str);
//        fatalError("failed to fined field metadata");
//    } else {
//        typeInfo = result.getType();
//    }
//
//    auto fieldType = FieldType(typeInfo.getMetadata());
    FieldType fieldType(metadata);
    fieldType.setIndirect(field.isIndirectCase());
    return {name, fieldType};
}

struct ReflectionMirrorImpl {

    const Metadata *type;

    virtual intptr_t recursiveCount() const = 0;

    virtual intptr_t recursiveChildOffset(intptr_t index) const = 0;

    virtual const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) = 0;

    virtual ~ReflectionMirrorImpl() {}
};

struct TupleImpl : ReflectionMirrorImpl {
    intptr_t recursiveCount() const override {
        return metadata()->numElements;
    }

    intptr_t recursiveChildOffset(intptr_t i) const override {
        if (i < 0 || size_t(i) > metadata()->numElements) {
            fatalError("Swift mirror subscript bounds check failure");
        }
        return metadata()->getElement(i).offset;
    }

    const Metadata *recursiveChildMetadata(
        intptr_t i,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        if (i < 0 || size_t(i) > metadata()->numElements) {
            fatalError("Swift mirror subscript bounds check failure");
        }

        // Determine whether there is a label.
        bool hasLabel = false;
        if (const char *labels = metadata()->labels) {
            const char *space = strchr(labels, ' ');
            for (intptr_t j = 0; j != i && space; ++j) {
                labels = space + 1;
                space = strchr(labels, ' ');
            }

            // If we have a label, create it.
            if (labels && space && labels != space) {
                *outName = strndup(labels, space - labels);
                hasLabel = true;
            }
        }

        if (!hasLabel) {
            // The name is the stringized element number '.0'.
            char *str;
            asprintf(&str, ".%" PRIdPTR, i);
            *outName = str;
        }

        *outFreeFunc = [](const char *str) { free(const_cast<char *>(str)); };

        return metadata()->getElement(i).type;
    }

private:
    const TupleTypeMetadata* metadata() const {
        return static_cast<const TupleTypeMetadata*>(type);
    }
};

struct StructImpl : ReflectionMirrorImpl {

    bool isReflectable() const {
        return metadata()->getDescription()->isReflectable();
    }

    intptr_t recursiveCount() const override {
        if (!isReflectable()) {
            return 0;
        }
        return metadata()->getDescription()->numFields;
    }

    intptr_t recursiveChildOffset(intptr_t i) const override {
        if (i < 0 || size_t(i) > metadata()->getDescription()->numFields) {
            fatalError("Swift mirror subscript bounds check failure");
        }

        // Load the offset from its respective vector.
        return metadata()->getFieldOffsets()[i];
    }

    const Metadata *recursiveChildMetadata(
        intptr_t i,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        const char *name = nullptr;
        FieldType fieldInfo;
        std::tie(name, fieldInfo) = getFieldAt(type, i);
        assert(!fieldInfo.isIndirect() && "indirect struct fields not implemented");

        *outName = name;
        *outFreeFunc = nullptr;

        return fieldInfo.getType();
    }

private:
    const StructMetadata* metadata() const {
        return static_cast<const StructMetadata*>(type);
    }
};

struct EnumImpl : ReflectionMirrorImpl {
    intptr_t recursiveCount() const override {
        return 0;
    }

    intptr_t recursiveChildOffset(intptr_t index) const override {
        return 0;
    }

    const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        return nullptr;
    }
};

struct ClassImpl : ReflectionMirrorImpl {

    bool isReflectable() const {
        return metadata()->getDescription()->isReflectable();
    }

    intptr_t count() const {
        if (!isReflectable())
            return 0;

        auto description = metadata()->getDescription();
        auto count = description->numFields;

        return count;
    }

    bool hasSuperclassMirror() const {
        return ((metadata()->getDescription()->superclassType)
                && (metadata()->superclass)
                && (metadata()->superclass->isTypeMetadata()));
    }

    ClassImpl superclassMirror() const {
        if (metadata()->getDescription()->superclassType) {
            if (const ClassMetadata *theSuperclass = metadata()->superclass) {
                ClassImpl impl;
                impl.type = theSuperclass;
                return impl;
            }
        }
        fatalError("No superclass mirror found");
    }
    
    intptr_t recursiveCount() const override {
        if (hasSuperclassMirror()) {
            return superclassMirror().recursiveCount() + count();
        }

        return count();
    }

    intptr_t childOffset(intptr_t i) const {
        auto description = metadata()->getDescription();

        if (i < 0 || sizeof(i) > description->numFields)
            fatalError("Swift mirror subscript bounds check failure");

        uintptr_t fieldOffset;
        if (usesNativeSwiftReferenceCounting(metadata())) {
            fieldOffset = metadata()->getFieldOffsets()[i];
        } else {
#if __APPLE__
            Ivar *ivars = class_copyIvarList(
                reinterpret_cast<Class>(const_cast<ClassMetadata *>(metadata())),
                nullptr
            );
            fieldOffset = ivar_getOffset(ivars[i]);
            free(ivars);
#else
            fatalError("Object appears to be Objective-C, but no runtime.");
#endif
        }
        return (intptr_t)fieldOffset;
    }

    intptr_t recursiveChildOffset(intptr_t i) const override {
        if (hasSuperclassMirror()) {
            ClassImpl superMirror = superclassMirror();
            intptr_t superclassFieldCount = superMirror.recursiveCount();

            if (i < superclassFieldCount) {
                return superMirror.recursiveChildOffset(i);
            } else {
                i -= superclassFieldCount;
            }
        }

        return childOffset(i);
    }

    const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        fatalError("unimplemented");
    }

private:
    const ClassMetadata *metadata() const {
        return static_cast<const ClassMetadata*>(type);
    }
};

#if __APPLE__
struct ObjCClassImpl : ClassImpl {

    intptr_t recursiveCount() const override {
        return 0;
    }

    intptr_t recursiveChildOffset(intptr_t index) const override {
        fatalError("Cannot get children of Objective-C objects");
    }

    const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        fatalError("Cannot get children of Objective-C objects");
    }
};
#endif

// MARK: ReflectionMirror

struct MetatypeImpl : ReflectionMirrorImpl {
    intptr_t recursiveCount() const override {
        return 0;
    }

    intptr_t recursiveChildOffset(intptr_t index) const override {
        fatalError("Metatypes have no children.");
    }

    const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        fatalError("Metatypes have no children.");
    }
};

struct OpaqueImpl : ReflectionMirrorImpl {
    intptr_t recursiveCount() const override {
        return 0;
    }

    intptr_t recursiveChildOffset(intptr_t index) const override {
        fatalError("Opaque types have no children.");
    }

    const Metadata *recursiveChildMetadata(
        intptr_t index,
        const char **outName,
        void (**outFreeFunc)(const char *)
    ) override {
        fatalError("Opaque types have no children.");
    }
};

template <typename F>
auto call(const Metadata *type, const F &f) -> decltype(f(nullptr)) {
    auto call = [&](ReflectionMirrorImpl *impl) {
        impl->type = type;
        return f(impl);
    };

    auto callClass = [&] {
        const Metadata *passedType;
//        // Get the runtime type of the object.
//        const void *obj = *reinterpret_cast<const void * const *>(value);
//        auto isa = _swift_getClass(obj);
//
//        // Look through artificial subclasses.
//        while (isa->isTypeMetadata() && isa->isArtificialSubclass()) {
//            isa = isa->Superclass;
//        }
//        passedType = isa;

//#if __APPLE__
//        // If this is a pure ObjC class, reflect it using ObjC's runtime facilities.
//        // ForeignClass (e.g. CF classes) manifests as a NULL class object.
//        auto *classObject = passedType->getClassObject();
//        if (classObject == nullptr || !classObject->isTypeMetadata()) {
//            ObjCClassImpl impl;
//            return call(&impl);
//        }
//#endif

        // Otherwise, use the native Swift facilities.
        ClassImpl impl;
        return call(&impl);
    };

    switch (type->getKind()) {
        case MetadataKind::Tuple: {
            TupleImpl impl;
            return call(&impl);
        }

        case MetadataKind::Struct: {
            StructImpl impl;
            return call(&impl);
        }

        case MetadataKind::Enum:
        case MetadataKind::Optional: {
            EnumImpl impl;
            return call(&impl);
        }

        case MetadataKind::ObjCClassWrapper:
        case MetadataKind::ForeignClass:
        case MetadataKind::Class: {
            return callClass();
        }

        case MetadataKind::Metatype:
        case MetadataKind::ExistentialMetatype: {
            MetatypeImpl impl;
            return call(&impl);
        }

        case MetadataKind::Opaque: {
//#if __APPLE__
//            // If this is the AnyObject type, use the dynamic type of the
//            // object reference.
//            if (type == &METADATA_SYM(BO).base) {
//                return callClass();
//            }
//#endif
//            // If this is the Builtin.NativeObject type, and the heap object is a
//            // class instance, use the dynamic type of the object reference.
//            if (type == &METADATA_SYM(Bo).base) {
//                const HeapObject *obj
//                = *reinterpret_cast<const HeapObject * const*>(value);
//                if (obj->metadata->getKind() == MetadataKind::Class) {
//                    return callClass();
//                }
//            }
//            SWIFT_FALLTHROUGH;
        }

        default:
            break;

        // Types can't have these kinds.
        case MetadataKind::HeapLocalVariable:
        case MetadataKind::HeapGenericLocalVariable:
        case MetadataKind::ErrorObject:
            fatalError("Swift mirror lookup failure");
    }

    // If we have an unknown kind of type, or a type without special handling,
    // treat it as opaque.
    OpaqueImpl impl;
    return call(&impl);
}

} // end namespace reflection_mirror

} // end anonymous namespace

// MARK: - Exported functions

uintptr_t FEFSRH_getMetadataKind(const void *type) {
    return uintptr_t(static_cast<const Metadata*>(type)->getKind());
}

intptr_t FEFSRH_reflectionMirror_recursiveCount(const void *type) {
    return reflection_mirror::call(static_cast<const Metadata*>(type),
                                   [](reflection_mirror::ReflectionMirrorImpl *impl) {
                                      return impl->recursiveCount();
                                   });
}

const void *FEFSRH_reflectionMirror_recursiveChildMetadata(
    const void *type,
    intptr_t index,
    const char **outName,
    void (**outFreeFunc)(const char *)
) {
    return reflection_mirror::call(static_cast<const Metadata*>(type),
                                   [&](reflection_mirror::ReflectionMirrorImpl *impl) {
                                      return impl->recursiveChildMetadata(index,
                                                                          outName,
                                                                          outFreeFunc);
                                   });
}

intptr_t FEFSRH_reflectionMirror_recursiveChildOffset(const void *type,
                                                      intptr_t index) {
    return reflection_mirror::call(static_cast<const Metadata*>(type),
                                   [&](reflection_mirror::ReflectionMirrorImpl *impl) {
                                      return impl->recursiveChildOffset(index);
                                   });
}
