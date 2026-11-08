#pragma once

#include <cstddef>
#include <string_view>

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct Expr;
struct Logic4Vec;
struct QueueObject;
struct Stmt;
class SimContext;
class Arena;

QueueObject* ElementQueueOfSelect(const Expr* sel, SimContext& ctx,
                                  Arena& arena, bool allocate);

const QueueObject* AssocElementQueueAt(const AssocArrayObject& aa,
                                       const Logic4Vec& key, Arena& arena);

bool SelectsElementQueue(const Expr* sel, SimContext& ctx, Arena& arena);

QueueObject* ElementQueueFromItem(const QueueObject* outer, const Expr* item,
                                  SimContext& ctx, Arena& arena);

const QueueObject* ElementQueueOrDefault(const QueueObject& outer, size_t pos,
                                         Arena& arena);

void BindElementQueueIterator(const QueueObject& outer, size_t pos,
                              std::string_view iter_name, SimContext& ctx,
                              Arena& arena);

bool FillQueueOfQueues(QueueObject* q, const Expr* pattern, SimContext& ctx,
                       Arena& arena);

bool TryCopyElementQueueToArray(const Stmt* stmt, const ArrayInfo& dst,
                                SimContext& ctx, Arena& arena);

}  // namespace delta
