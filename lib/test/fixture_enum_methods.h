#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

#include <gtest/gtest.h>

using namespace delta;

struct EnumFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  Variable* RegisterEnum(
      std::string_view var_name, std::string_view type_name,
      const std::vector<std::pair<std::string, uint64_t>>& members) {
    EnumTypeInfo info;
    char* tn = arena.AllocString(type_name.data(), type_name.size());
    info.type_name = std::string_view(tn, type_name.size());
    for (auto& [name, val] : members) {
      EnumMemberInfo m;
      char* mn = arena.AllocString(name.c_str(), name.size());
      m.name = std::string_view(mn, name.size());
      m.value = val;
      info.members.push_back(m);
    }
    ctx.RegisterEnumType(info.type_name, info);

    auto* var = ctx.CreateVariable(var_name, 32);
    var->value = MakeLogic4VecVal(arena, 32, members[0].second);
    ctx.SetVariableEnumType(var_name, info.type_name);
    return var;
  }

  Expr* MakeEnumMethodCall(std::string_view var_name,
                           std::string_view method_name) {
    return MakeEnumMethodCallWithArgs(var_name, method_name, {});
  }

  Expr* MakeEnumMethodCallWithArgs(std::string_view var_name,
                                   std::string_view method_name,
                                   std::vector<Expr*> args) {
    auto* id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = var_name;

    auto* member = arena.Create<Expr>();
    member->kind = ExprKind::kIdentifier;
    member->text = method_name;

    auto* access = arena.Create<Expr>();
    access->kind = ExprKind::kMemberAccess;
    access->lhs = id;
    access->rhs = member;

    auto* call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->lhs = access;
    call->args = std::move(args);
    return call;
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }
};
