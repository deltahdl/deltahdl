#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

namespace {

struct PlaTaskKind {
  bool valid = false;
  bool is_async = false;
  enum class Logic : std::uint8_t {
    kAnd,
    kOr,
    kNand,
    kNor
  } logic = Logic::kAnd;
  bool is_plane = false;
};

bool DecodePlaType(std::string_view type, PlaTaskKind& k) {
  if (type == "sync") {
    k.is_async = false;
  } else if (type == "async") {
    k.is_async = true;
  } else {
    return false;
  }
  return true;
}

bool DecodePlaLogic(std::string_view logic, PlaTaskKind& k) {
  if (logic == "and") {
    k.logic = PlaTaskKind::Logic::kAnd;
  } else if (logic == "or") {
    k.logic = PlaTaskKind::Logic::kOr;
  } else if (logic == "nand") {
    k.logic = PlaTaskKind::Logic::kNand;
  } else if (logic == "nor") {
    k.logic = PlaTaskKind::Logic::kNor;
  } else {
    return false;
  }
  return true;
}

bool DecodePlaFormat(std::string_view format, PlaTaskKind& k) {
  if (format == "array") {
    k.is_plane = false;
  } else if (format == "plane") {
    k.is_plane = true;
  } else {
    return false;
  }
  return true;
}

PlaTaskKind ClassifyPlaTask(std::string_view callee) {
  PlaTaskKind k;
  if (callee.empty() || callee.front() != '$') return k;
  std::string_view rest = callee.substr(1);
  auto take = [&rest]() -> std::string_view {
    auto pos = rest.find('$');
    std::string_view tok = rest.substr(0, pos);
    rest = pos == std::string_view::npos ? std::string_view{}
                                         : rest.substr(pos + 1);
    return tok;
  };
  std::string_view type = take();
  std::string_view logic = take();
  std::string_view format = take();
  if (!rest.empty()) return k;
  if (!DecodePlaType(type, k)) return k;
  if (!DecodePlaLogic(logic, k)) return k;
  if (!DecodePlaFormat(format, k)) return k;
  k.valid = true;
  return k;
}

Logic4Word PlaBitAt(const Logic4Vec& v, uint32_t p) {
  if (p >= v.width) return {0, 0};
  uint32_t w = p / 64, b = p % 64;
  return {(v.words[w].aval >> b) & 1ULL, (v.words[w].bval >> b) & 1ULL};
}

void PlaSetBit(Logic4Vec& v, uint32_t pos, Logic4Word bit) {
  if (pos >= v.width) return;
  uint32_t w = pos / 64, b = pos % 64;
  v.words[w].aval |= (bit.aval & 1ULL) << b;
  v.words[w].bval |= (bit.bval & 1ULL) << b;
}

Logic4Word PlaInputTerm(const PlaTaskKind& k, Logic4Word code,
                        Logic4Word in_bit, bool& participates) {
  participates = true;
  if (k.is_plane) {
    if (code.bval == 0) {
      return code.aval == 1 ? in_bit : Logic4Not(in_bit);
    }
    if (code.aval == 1) {
      return Logic4Word{0, 1};
    }
    participates = false;
    return Logic4Word{0, 0};
  }
  participates = code.aval == 1 && code.bval == 0;
  return in_bit;
}

Logic4Word PlaReduceWord(const PlaTaskKind& k, const Logic4Vec& mem_word,
                         const Logic4Vec& inputs, uint32_t n) {
  bool is_and = k.logic == PlaTaskKind::Logic::kAnd ||
                k.logic == PlaTaskKind::Logic::kNand;
  Logic4Word acc = is_and ? Logic4Word{1, 0} : Logic4Word{0, 0};
  for (uint32_t p = 0; p < n; ++p) {
    Logic4Word code = PlaBitAt(mem_word, p);
    Logic4Word in_bit = PlaBitAt(inputs, p);
    bool participates = true;
    Logic4Word term = PlaInputTerm(k, code, in_bit, participates);
    if (participates) {
      acc = is_and ? Logic4And(acc, term) : Logic4Or(acc, term);
    }
  }
  bool invert = k.logic == PlaTaskKind::Logic::kNand ||
                k.logic == PlaTaskKind::Logic::kNor;
  return invert ? Logic4Not(acc) : acc;
}

void EvaluatePla(const Expr* call, const PlaTaskKind& k, SimContext& ctx,
                 Arena& arena) {
  if (call->args.size() < 3 || !call->args[0] || !call->args[1] ||
      !call->args[2])
    return;
  if (call->args[0]->kind != ExprKind::kIdentifier) return;
  const ArrayInfo* ai = ctx.FindArrayInfo(call->args[0]->text);
  if (!ai || ai->size == 0) return;
  uint32_t n = ai->elem_width;
  uint32_t m = ai->size;
  Logic4Vec inputs = EvalExpr(call->args[1], ctx, arena);
  Logic4Vec result = MakeLogic4Vec(arena, m);
  std::string mem_name(call->args[0]->text);
  for (uint32_t j = 0; j < m; ++j) {
    std::string elem = mem_name + "[" + std::to_string(ai->lo + j) + "]";
    Variable* word_var = ctx.FindVariable(elem);
    Logic4Vec word = word_var ? word_var->value : MakeLogic4Vec(arena, n);
    Logic4Word out_bit = PlaReduceWord(k, word, inputs, n);
    PlaSetBit(result, m - 1 - j, out_bit);
  }
  PerformBlockingAssign(call->args[2], result, ctx, arena);
}

void CollectPlaInputSignals(const Expr* e, std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  CollectPlaInputSignals(e->lhs, out);
  CollectPlaInputSignals(e->rhs, out);
  CollectPlaInputSignals(e->base, out);
  CollectPlaInputSignals(e->index, out);
  CollectPlaInputSignals(e->index_end, out);
  for (auto* a : e->args) CollectPlaInputSignals(a, out);
  for (auto* el : e->elements) CollectPlaInputSignals(el, out);
}

void InstallAsyncPlaWatchers(const Expr* expr, const PlaTaskKind& k,
                             SimContext& ctx, Arena& arena) {
  auto reeval = [expr, k, &ctx, &arena]() -> bool {
    EvaluatePla(expr, k, ctx, arena);
    return false;
  };
  std::vector<std::string_view> names;
  if (expr->args.size() >= 2) CollectPlaInputSignals(expr->args[1], names);
  for (auto name : names) {
    if (Variable* v = ctx.FindVariable(name)) v->AddWatcher(reeval);
  }
  if (!expr->args.empty() && expr->args[0] &&
      expr->args[0]->kind == ExprKind::kIdentifier) {
    if (const ArrayInfo* ai = ctx.FindArrayInfo(expr->args[0]->text)) {
      std::string mem_name(expr->args[0]->text);
      for (uint32_t j = 0; j < ai->size; ++j) {
        std::string elem = mem_name + "[" + std::to_string(ai->lo + j) + "]";
        if (Variable* v = ctx.FindVariable(elem)) v->AddWatcher(reeval);
      }
    }
  }
}

}  // namespace

bool TryEvalPlaSystemTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  PlaTaskKind k = ClassifyPlaTask(expr->callee);
  if (!k.valid) return false;
  EvaluatePla(expr, k, ctx, arena);
  if (k.is_async) {
    InstallAsyncPlaWatchers(expr, k, ctx, arena);
  }
  return true;
}

}  // namespace delta
