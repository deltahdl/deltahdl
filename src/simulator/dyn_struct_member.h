#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
struct QueueObject;
struct StructFieldInfo;

QueueObject* DynMemberQueue(const Logic4Vec& handle);
std::vector<const QueueObject*> DynMemberQueues();

QueueObject* DynMemberEmpty(const StructFieldInfo& field);

QueueObject* NewDynMember(const StructFieldInfo& field, Logic4Vec& handle,
                          Arena& arena);

QueueObject* DynMemberForWrite(Logic4Vec& holder, uint32_t offset,
                               const StructFieldInfo& field, Arena& arena);

}  // namespace delta
