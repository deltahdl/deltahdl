#pragma once

namespace delta {

struct AssocArrayObject;
struct Expr;
class SimContext;
class Arena;

AssocArrayObject* ElementAssocOfSelect(const Expr* sel, SimContext& ctx,
                                       Arena& arena, bool allocate);

}  // namespace delta
