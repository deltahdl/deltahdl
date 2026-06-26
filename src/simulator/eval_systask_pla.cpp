#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// ---------------------------------------------------------------------------
// §20.16 / §20.16.1: programmable logic array (PLA) modeling system tasks.
// ---------------------------------------------------------------------------

namespace {

// §20.16, Table 20-12: a PLA task is named $<array_type>$<logic>$<format>.
// These are the decoded components that drive evaluation.
struct PlaTaskKind {
  bool valid = false;
  bool is_async = false;  // §20.16.1: asynchronous vs synchronous array
  enum class Logic : std::uint8_t {
    kAnd,
    kOr,
    kNand,
    kNor
  } logic = Logic::kAnd;
  bool is_plane = false;  // §20.16.4 format: array vs plane
};

// §20.16, Table 20-12: decode the array-type component, setting is_async.
// Returns false when the component is not "sync" or "async".
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

// §20.16, Table 20-12: decode the logic component, setting the logic field.
// Returns false when the component is not one of and/or/nand/nor.
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

// §20.16.4: decode the format component, setting is_plane. Returns false when
// the component is not "array" or "plane".
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

// §20.16: split a callee into its three dollar-separated components and decide
// whether it names one of the sixteen tasks of Table 20-12. This mirrors the
// elaborator's IsPlaSystemTask recognizer but also keeps the decoded fields.
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
  if (!rest.empty()) return k;  // more than three components
  if (!DecodePlaType(type, k)) return k;
  if (!DecodePlaLogic(logic, k)) return k;
  if (!DecodePlaFormat(format, k)) return k;
  k.valid = true;
  return k;
}

// A single 4-state bit at position `p` of `v`, packed into bit position 0.
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

// §20.16.1: reduce the input terms selected by one personality word into a
// single output-term bit. The logic component fixes whether the participating
// inputs are AND- or OR-reduced, and the complemented forms (nand/nor) invert
// the result.
//
// §20.16.4 defines two personality formats, chosen by the format component of
// the task name (array vs plane). In the array format a personality bit of 1
// takes the input value and any other bit does not take it. In the plane
// (Berkeley Espresso) format the bit instead selects how the input
// participates: 0 takes the complemented input, 1 takes the true input, a
// don't-care (z, and the equivalent ?) drops the input from the reduction, and
// x takes the worst case by contributing an unknown. In the 4-state encoding a
// personality bit holds 0 as {0,0}, 1 as {1,0}, x as {1,1} and z/? as {0,1}.
// §20.16.4: map one personality code and its input bit to the term that the
// input contributes to the reduction. Sets `participates` to false when the
// personality code drops the input from the reduction (array format != 1, or
// plane-format z/? don't-care). The returned term is meaningful only when
// `participates` is true.
Logic4Word PlaInputTerm(const PlaTaskKind& k, Logic4Word code,
                        Logic4Word in_bit, bool& participates) {
  participates = true;
  if (k.is_plane) {
    // §20.16.4 plane-format (Espresso) personality codes.
    if (code.bval == 0) {
      // 1 takes the true input value, 0 takes the complemented input value.
      return code.aval == 1 ? in_bit : Logic4Not(in_bit);
    }
    if (code.aval == 1) {
      // x: take the worst case of the input value - contribute an unknown.
      return Logic4Word{0, 1};
    }
    // z (and the equivalent ?): do-not-care, the input does not participate.
    participates = false;
    return Logic4Word{0, 0};
  }
  // §20.16.4 array-format personality codes: 1 takes the input value.
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

// §20.16.1: perform one evaluation of the array from its current personality
// memory and input terms and drive the output terms with no delay. Silently
// does nothing when the call is malformed or the personality memory is unknown.
void EvaluatePla(const Expr* call, const PlaTaskKind& k, SimContext& ctx,
                 Arena& arena) {
  if (call->args.size() < 3 || !call->args[0] || !call->args[1] ||
      !call->args[2])
    return;
  if (call->args[0]->kind != ExprKind::kIdentifier) return;
  const ArrayInfo* ai = ctx.FindArrayInfo(call->args[0]->text);
  if (!ai || ai->size == 0) return;
  uint32_t n = ai->elem_width;  // §20.16.3: word width == number of input terms
  uint32_t m = ai->size;        // depth == number of output terms
  Logic4Vec inputs = EvalExpr(call->args[1], ctx, arena);
  Logic4Vec result = MakeLogic4Vec(arena, m);
  std::string mem_name(call->args[0]->text);
  for (uint32_t j = 0; j < m; ++j) {
    std::string elem = mem_name + "[" + std::to_string(ai->lo + j) + "]";
    Variable* word_var = ctx.FindVariable(elem);
    Logic4Vec word = word_var ? word_var->value : MakeLogic4Vec(arena, n);
    Logic4Word out_bit = PlaReduceWord(k, word, inputs, n);
    // §20.16.3: terms and memory are specified in ascending order, so the
    // lowest memory address corresponds to the most significant output term.
    PlaSetBit(result, m - 1 - j, out_bit);
  }
  // §20.16.1: "the output terms are updated without any delay" - an immediate
  // (blocking) write into the output-terms lvalue.
  PerformBlockingAssign(call->args[2], result, ctx, arena);
}

// Gathers the simple signal names referenced anywhere in the input-terms
// argument, so the asynchronous forms can watch each one for changes.
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

// §20.16.1: the asynchronous forms re-evaluate on their own whenever an input
// term changes value or any word of the personality memory is changed. Install
// a persistent watcher on each input signal and each memory word that
// recomputes and re-drives the outputs.
void InstallAsyncPlaWatchers(const Expr* expr, const PlaTaskKind& k,
                             SimContext& ctx, Arena& arena) {
  auto reeval = [expr, k, &ctx, &arena]() -> bool {
    EvaluatePla(expr, k, ctx, arena);
    return false;  // keep watching
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
  // §20.16.1: both array types evaluate immediately when the task is called and
  // update the outputs without delay. For the synchronous forms this single
  // evaluation is the whole behavior - the call site controls the time at which
  // the array is evaluated and the outputs updated.
  EvaluatePla(expr, k, ctx, arena);
  if (k.is_async) {
    InstallAsyncPlaWatchers(expr, k, ctx, arena);
  }
  return true;
}

}  // namespace delta
