#if !canImport(Darwin) && swift(>=5.3)
@_spi(Reflection) import func Swift._forEachField
#else
import CForEachFieldSwiftRuntimeHelpers

extension UnsafeRawPointer {
    fileprivate static func toOpaque(_ type: Any.Type) -> UnsafeRawPointer {
        return unsafeBitCast(type, to: UnsafeRawPointer.self)
    }

    fileprivate func toType() -> Any.Type {
        return unsafeBitCast(self, to: Any.Type.self)
    }
}

private typealias NameFreeFunc = @convention(c) (UnsafePointer<CChar>?) -> Void

private func forEachFieldImplementation(
    of type: Any.Type,
    options: EachFieldOptions = [],
    body: (UnsafePointer<CChar>, Int, Any.Type, MetadataKind) -> Bool
) -> Bool {
    // Require class type iff `.classType` is included as an option
    if MetadataKind(type).isAnyKindOfClass != options.contains(.classType) {
        return false
    }

    let childCount = getRecursiveChildCount(.toOpaque(type))
    for i in 0 ..< childCount {
        let offset = getChildOffset(.toOpaque(type), index: i)

        var nameC: UnsafePointer<CChar>? = nil
        var freeFunc: NameFreeFunc? = nil
        let childType = getChildMetadata(.toOpaque(type),
                                         index: i,
                                         outName: &nameC,
                                         outFreeFunc: &freeFunc)
        defer { freeFunc?(nameC) }
        let kind = MetadataKind(childType.toType())

        if !body(nameC!, offset, childType.toType(), kind) {
            return false
        }
    }

    return true
}

extension MetadataKind {
    fileprivate init(_ type: Any.Type) {
        self.init(rawValueOrUnknown: metadataKind(.toOpaque(type)))
    }

    fileprivate var isAnyKindOfClass: Bool {
        switch self {
        case .class, .objcClassWrapper, .foreignClass:
            return true
        default:
            return false
        }
    }
}
#endif

/// Options for calling `forEachField(of:options:body:)`.
public struct EachFieldOptions: OptionSet {

    public var rawValue: UInt32

    public init(rawValue: UInt32) {
        self.rawValue = rawValue
    }

    /// Require the top-level type to be a class.
    ///
    /// If this is not set, the top-level type is required to be a struct or
    /// tuple.
    public static var classType = EachFieldOptions(rawValue: 1 << 0)

    /// Ignore fields that can't be introspected.
    ///
    /// If not set, the presence of things that can't be introspected causes
    /// the function to immediately return `false`.
    public static var ignoreUnknown = EachFieldOptions(rawValue: 1 << 1)
}

/// The metadata "kind" for a type.
public enum MetadataKind: UInt {
    // With "flags":
    // runtimePrivate = 0x100
    // nonHeap = 0x200
    // nonType = 0x400

    case `class`                  = 0x000
    case `struct`                 = 0x200  // 0 | nonHeap
    case `enum`                   = 0x201  // 1 | nonHeap
    case optional                 = 0x202  // 2 | nonHeap
    case foreignClass             = 0x203  // 3 | nonHeap
    case opaque                   = 0x300  // 0 | runtimePrivate | nonHeap
    case tuple                    = 0x301  // 1 | runtimePrivate | nonHeap
    case function                 = 0x302  // 2 | runtimePrivate | nonHeap
    case existential              = 0x303  // 3 | runtimePrivate | nonHeap
    case metatype                 = 0x304  // 4 | runtimePrivate | nonHeap
    case objcClassWrapper         = 0x305  // 5 | runtimePrivate | nonHeap
    case existentialMetatype      = 0x306  // 6 | runtimePrivate | nonHeap
    case heapLocalVariable        = 0x400  // 0 | nonType
    case heapGenericLocalVariable = 0x500  // 0 | nonType | runtimePrivate
    case errorObject              = 0x501  // 1 | nonType | runtimePrivate
    case simpleTask               = 0x502  // 2 | nonType | runtimePrivate
    case unknown                  = 0xffff

    fileprivate init(rawValueOrUnknown: UInt) {
        if let result = MetadataKind(rawValue: rawValueOrUnknown) {
            self = result
        } else {
            self = .unknown
        }
    }
}

/// Calls the given closure on every field of the specified type.
///
/// If `body` returns `false` for any field, no additional fields are visited.
///
/// - Parameters:
///   - type: The type to inspect.
///   - options: Options to use when reflecting over `type`.
///   - body: A closure to call with information about each field in `type`.
///     The parameters to `body` are a pointer to a C string holding the name
///     of the field, the offset of the field in bytes, the type of the field,
///     and the `MetadataKind` of the field's type.
/// - Returns: `true` if every invocation of `body` returns `true`; otherwise,
///   `false`.
@discardableResult
public func forEachField(
    of type: Any.Type,
    options: EachFieldOptions = [],
    body: (UnsafePointer<CChar>, Int, Any.Type, MetadataKind) -> Bool
) -> Bool {
#if !canImport(Darwin) && swift(>=5.3)
    // On non-darwin platforms, use the stdlib implementation whenever possible,
    // because the ABI there is not stable.
    return _forEachField(
        of: type,
        options: _EachFieldOptions(rawValue: options.rawValue),
        body: { name, offset, type, kind in
            body(name, offset, type, MetadataKind(rawValueOrUnknown: kind.rawValue))
        }
    )
#else
    // Always use our own implementaion instead of the stdlib one
    // so that our clients don't get their apps rejected by the App Store
    // for private API usage.
    //
    // Since Swift's ABI is stable on Darwin platforms, this should always work.
    //
    // On non-Darwin platforms prior to Swift 5.3, our implementation has been also
    // verified to work.
    return forEachFieldImplementation(of: type, options: options, body: body)
#endif
}
