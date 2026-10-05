#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct VpiObject;

// §37.17 and §38.19: the element of the queue, dynamic array or associative
// array `array` at `index` (a key, for an associative array keyed by an
// integral type), made with `build` the first time it is asked for and kept
// among the array's children after. Null where the array holds no element
// there. Its value is a copy of the stored element, refreshed here.
VpiObject* VpiCollectionElement(VpiObject& array, int index,
                                const VpiAttachBuild& build);

// Copies an element of a queue, dynamic or associative array in from the store
// it lives in, a member of an unpacked struct or union in from the bits of the
// var holding it, and a property variable of a class obj in from the object,
// before its value is read; nothing for any other object.
void VpiRefreshElementCopy(VpiObject& element);

// Copies a value written to such an element or member back where it lives.
void VpiStoreElementCopy(VpiObject& element);

}  // namespace delta
