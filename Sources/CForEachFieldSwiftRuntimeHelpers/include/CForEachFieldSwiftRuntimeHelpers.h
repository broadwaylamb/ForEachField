#ifndef CForEachFieldSwiftRuntimeHelpers_h
#define CForEachFieldSwiftRuntimeHelpers_h

#include <stdbool.h>
#include <stdint.h>

#if __has_attribute(swift_name)
# define FEFSRH_SWIFT_NAME(_name) __attribute__((swift_name(#_name)))
#else
# define FEFSRH_SWIFT_NAME(_name)
#endif

#ifdef __cplusplus
extern "C" {
#endif

uintptr_t
FEFSRH_getMetadataKind(const void * _Nonnull type)
    FEFSRH_SWIFT_NAME(metadataKind(_:));

intptr_t
FEFSRH_reflectionMirror_recursiveCount(const void * _Nonnull type)
    FEFSRH_SWIFT_NAME(getRecursiveChildCount(_:));

const void* _Nonnull
FEFSRH_reflectionMirror_recursiveChildMetadata(
    const void * _Nonnull type,
    intptr_t index,
    const char * _Nullable * _Nonnull outName,
    void (*_Nullable * _Nonnull outFreeFunc)(const char * _Nullable)
) FEFSRH_SWIFT_NAME(getChildMetadata(_:index:outName:outFreeFunc:));

intptr_t FEFSRH_reflectionMirror_recursiveChildOffset(
    const void * _Nonnull type,
    intptr_t index
) FEFSRH_SWIFT_NAME(getChildOffset(_:index:));

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* CForEachFieldSwiftRuntimeHelpers_h */
