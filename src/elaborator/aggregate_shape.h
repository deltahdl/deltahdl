#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct StructMember;

// What the structure and union rules read besides the type they judge.
struct AggregateShapeCtx {
  // The typedefs, typedef dimensions and class names a member's type and its
  // unpacked dimensions are resolved against.
  const TypeShapeTables& tables;
  // The parameter scope a member's default value is judged constant against,
  // or null where the declaration has none to judge it against.
  const ScopeMap* member_default_scope;
  DiagEngine& diag;
};

// §7.2 to §7.3.2 (printed pages 146–152): reports, at `loc`, each rule a
// structure or union type breaks:
// - footnote 17's `packed` with a packed dimension;
// - footnote 20's placement of `void` members and random qualifiers;
// - the member types a packed structure or union admits, with a hard packed
//   union's equal sizes;
// - §7.2.2's member defaults;
// - the chandles and dynamic types an untagged union may not hold;
// - §25.9's virtual interface members.
// A member is judged by the type it is written with, followed through a
// typedef name, and every structure or union written inline as a member is
// judged the same way at any depth. Anything other than a structure or union
// is left alone.
void CheckAggregateShape(const DataType& dtype, SourceLoc loc,
                         const AggregateShapeCtx& ctx);

// §6.18: the type the structure or union member `m` is written with when that
// is more than a keyword: a structure, union or enumeration written in place,
// or the type a typedef name stands for once every name in the chain is
// followed. Null for a keyword type and for a name that resolves to nothing,
// such as a class.
const DataType* MemberOwnType(const StructMember& m,
                              const TypedefMap& typedefs);

// Whether `type` is an unpacked structure or union: one written without
// `packed`, and for a union without `soft` either. False for null.
bool IsUnpackedAggregate(const DataType* type);

}  // namespace delta
