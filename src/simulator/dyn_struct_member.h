#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

class Arena;
struct QueueObject;
struct StructFieldInfo;

// §7.2 with §7.5: a member of an unpacked structure declared as a dynamic
// array holds a number of elements no layout fixes, so the structure's packed
// value holds a handle to them (kDynamicMemberHandleWidth bits) rather than
// the elements. The elements a handle names never change once another value
// may hold the handle -- a write goes to a copy under a new handle -- so a
// copy of the structure, by assignment, argument or construction, keeps the
// elements it was copied with.

// The elements the handle `handle` holds names; null for the zero handle,
// which a member never written holds, and for one with an unknown bit.
QueueObject* DynMemberQueue(const Logic4Vec& handle);

// An empty array of the elements the dynamic member `field` declares, which
// a member holding the zero handle reads as; shared, so never written.
QueueObject* DynMemberEmpty(const StructFieldInfo& field);

// A new empty array of the elements the dynamic member `field` declares, for
// a value of the member to be given, under a new handle `handle` receives.
QueueObject* NewDynMember(const StructFieldInfo& field, Logic4Vec& handle,
                          Arena& arena);

// The elements a write to the dynamic member `field`, held at bit `offset` of
// the structure value `holder`, goes to: a copy of those its handle names,
// none for the zero handle, under a new handle `holder` is given there.
QueueObject* DynMemberForWrite(Logic4Vec& holder, uint32_t offset,
                               const StructFieldInfo& field, Arena& arena);

}  // namespace delta
