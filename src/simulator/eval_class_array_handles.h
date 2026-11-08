#pragma once

#include <string_view>

#include "common/types.h"
#include "simulator/eval_function_internal.h"

namespace delta {

struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct Stmt;
class SimContext;
class Arena;

bool TryClassArrayElementNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

bool TryEvalClassArrayElementMember(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

Logic4Vec ConstructElementObject(const Expr* rhs, std::string_view class_type,
                                 SimContext& ctx, Arena& arena);

bool TryEvalElementObjectMember(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

bool ResolveElementObjectMethod(const Expr* access, SimContext& ctx,
                                Arena& arena, InstanceMethodInfo& info,
                                bool report_null);

bool TryEvalElementObjectMethodCall(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

ClassObject* DeclaredArrayElementObject(const Expr* expr, SimContext& ctx,
                                        Arena& arena,
                                        const ClassTypeInfo*& declared);

}  // namespace delta
