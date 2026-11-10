#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
struct AssocArrayObject;
class SimContext;
class Arena;

Logic4Vec AssocAllocValue(const AssocArrayObject* aa, Arena& arena);

Logic4Vec* AssocEntryForWrite(const Expr* sel, SimContext& ctx, Arena& arena);

bool TryWriteAssocMemberField(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

bool TryWriteAssocElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

void AllocateAssocEntryForModify(const Expr* lhs, SimContext& ctx,
                                 Arena& arena);

}  // namespace delta
