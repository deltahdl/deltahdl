#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct StructMember;

struct AggregateShapeCtx {
  const TypeShapeTables& tables;
  const ScopeMap* member_default_scope;
  DiagEngine& diag;
};

void CheckAggregateShape(const DataType& dtype, SourceLoc loc,
                         const AggregateShapeCtx& ctx);

const DataType* MemberOwnType(const StructMember& m,
                              const TypedefMap& typedefs);

DataType MemberWrittenType(const StructMember& m);

bool IsUnpackedAggregate(const DataType* type);

}  // namespace delta
