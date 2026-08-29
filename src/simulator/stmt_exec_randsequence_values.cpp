// The values a randsequence production is called with and the values it
// returns, which §18.17.7 states as one rule apiece: "Passing data to a
// production uses the same syntax as a task call", and, within a rule, "a
// variable is implicitly declared" for each value-returning production the
// rule names. EvalProductionActuals and BindProductionFormals answer the
// first, evaluating a call's actual arguments in the caller's scope and
// binding each formal by position once the production's own scope has been
// entered. BuildRuleValueCapture and BuildStepValueCapture answer the second,
// counting how many times a rule names each value-returning production so
// that one named more than once is registered as the 1..N array §18.17.7
// declares before any of its appearances generates. SlotForAppearance then
// says which implicit variable one appearance writes, and
// StoreRuleProductionValue creates that variable and stores the returned
// value into it.
//
// src/simulator/stmt_exec_randsequence.cpp holds the rest of the statement --
// §18.16's randcase, §18.17.1's weighted selection of a rule, the production
// list forms of §18.17.2 through §18.17.4, §18.17.5's rand join and the reach
// §18.17.6 gives break and return -- and is the only caller of the six
// functions named above.

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_randsequence_internal.h"

namespace delta {

// The two types below are also defined in
// src/simulator/stmt_exec_randsequence.cpp, which generates the productions
// these functions record and so names both types itself. A change to either
// definition has to be made in both files.

// §18.17.7: which productions a randsequence statement declares and whether one
// of them returns a value. Defined in src/simulator/stmt_exec_randsequence.cpp,
// which generates them.
const RsProduction* FindProduction(const Stmt* stmt, std::string_view name);
bool ProductionReturnsValue(const RsProduction* p);
bool ProductionReturnsString(const RsProduction* p);

// §18.17.7: passing data to a production uses the same syntax as a task call.
// Evaluate the actual arguments in the caller's scope, before the production's
// own scope is entered, sizing each to its formal's declared width.
std::vector<Logic4Vec> EvalProductionActuals(const RsProduction* production,
                                             const RsProductionItem& call,
                                             SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> actuals;
  actuals.reserve(call.args.size());
  for (size_t i = 0; i < call.args.size(); ++i) {
    uint32_t w = i < production->ports.size()
                     ? EvalTypeWidth(production->ports[i].data_type)
                     : 0;
    actuals.push_back(EvalExpr(call.args[i], ctx, arena, w));
  }
  return actuals;
}

// §18.17.7: a production creates a scope that encompasses all its rules and
// code blocks; formal arguments bound here are therefore available throughout
// the production. Bind each formal by position, falling back to its default
// value, then to zero, when no actual is supplied. The caller must have entered
// the production's scope.
void BindProductionFormals(const RsProduction* production,
                           const std::vector<Logic4Vec>& actuals,
                           SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < production->ports.size(); ++i) {
    const auto& port = production->ports[i];
    uint32_t w = EvalTypeWidth(port.data_type);
    Logic4Vec val;
    if (i < actuals.size()) {
      val = actuals[i];
    } else if (port.default_value != nullptr) {
      val = EvalExpr(port.default_value, ctx, arena, w);
    } else {
      val = MakeLogic4VecVal(arena, w ? w : 32, 0);
    }
    uint32_t vw = val.width ? val.width : (w ? w : 32);
    auto* var = ctx.CreateLocalVariable(port.name, vw);
    var->value = val;
  }
}

// §18.17.7: record one appearance of a value-returning production, giving it
// the next ordinal in the rule. Every appearance counts, including one written
// inside an if, repeat or case production: the clause gives the code block of
// `if (cond) D(5) else D(20)` the implicit declaration `int D[1:2]`, and the
// code block of `B repeat(5) C B` the declarations `int B[1:2]` and `int C`.
// A repeat counts its item once however many times it goes on to generate it.
static void CountRuleProductionItem(const Stmt* stmt,
                                    const RsProductionItem& item,
                                    RuleValueCapture& cap) {
  if (!ProductionReturnsValue(FindProduction(stmt, item.name))) return;
  cap.ordinal[&item] = ++cap.total[item.name];
}

// §18.17.7: count the appearances of every value-returning production one
// production of a rule names, reaching the items an if, repeat or case
// production generates as well as an item written directly in the rule.
static void CountRuleProductions(const Stmt* stmt, const RsProd& prod,
                                 RuleValueCapture& cap) {
  switch (prod.kind) {
    case RsProdKind::kItem:
      CountRuleProductionItem(stmt, prod.item, cap);
      return;
    case RsProdKind::kIf:
      CountRuleProductionItem(stmt, prod.if_true, cap);
      if (prod.has_else) CountRuleProductionItem(stmt, prod.if_false, cap);
      return;
    case RsProdKind::kRepeat:
      CountRuleProductionItem(stmt, prod.repeat_item, cap);
      return;
    case RsProdKind::kCase:
      for (const auto& ci : prod.case_items)
        CountRuleProductionItem(stmt, ci.item, cap);
      return;
    case RsProdKind::kCodeBlock:
      return;
  }
}

// §18.17.7: register the array shape of every production the counted
// appearances name more than once, so a code block can read an element before
// any generation has written one. A production named once needs no shape: its
// implicit variable is the scalar StoreRuleProductionValue creates.
static void RegisterRuleValueArrays(const Stmt* stmt,
                                    const RuleValueCapture& cap,
                                    SimContext& ctx) {
  for (const auto& [name, n] : cap.total) {
    if (n <= 1) continue;
    const auto* child = FindProduction(stmt, name);
    ArrayInfo info;
    info.lo = 1;
    info.size = static_cast<uint32_t>(n);
    uint32_t w = EvalTypeWidth(child->return_type);
    // §18.17.7: "the type is an array where the element type is the return
    // type of the production", so record the return type's kind for a read of
    // an element to consult. §6.16 then makes the element of a string array
    // that no generation wrote "", the empty string, rather than 32 bits of x;
    // every other return type EvalTypeWidth gives no width to keeps the
    // 32-bit carrier.
    info.elem_type_kind = child->return_type.kind;
    info.elem_width = w ? w : (ProductionReturnsString(child) ? 0 : 32);
    // §18.17: "The randsequence statement creates an automatic scope", and
    // §18.17.7 declares this array "within a rule", so the name stands for the
    // array only while that scope is on the stack. RegisterLocalArray puts the
    // shape in the same scope as the implicit variables
    // StoreRuleProductionValue creates, so PopScope takes both away together: a
    // variable of the design that shares the name is read as itself again once
    // the statement ends, and each activation of the rule sees its own shape.
    // §18.17.7's Example 2 needs the last of those, giving one production three
    // rules that name C once, twice and three times.
    ctx.RegisterLocalArray(name, info);
  }
}

// §18.17.7: within a rule, a variable is implicitly declared for each
// value-returning production the rule names. A production named once yields a
// scalar named after the production; a production named more than once yields
// an array indexed 1..N, with element i holding the value returned by the i-th
// appearance in syntactic order. Count the rule's appearances so a multiply
// appearing production can be registered as an array before any code block
// reads an element of it.
RuleValueCapture BuildRuleValueCapture(const Stmt* stmt, const RsRule& selected,
                                       SimContext& ctx) {
  RuleValueCapture cap;
  // Syntax 18-13 gives a rand join rule its productions as the
  // rs_production_items written after the keywords, which stand in
  // RsRule::rand_join_items and in no RsProd of RsRule::prods. A rule holds one
  // list or the other, so both are walked and the empty one contributes
  // nothing.
  for (const auto& item : selected.rand_join_items) {
    CountRuleProductionItem(stmt, item, cap);
  }
  for (const auto& prod : selected.prods) {
    CountRuleProductions(stmt, prod, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

// §18.17.5 interleaves a rand join operand's productions to a depth of 1, so
// what generates under the operand is the productions its own rule names rather
// than the operand itself. Count the appearances over the steps that expansion
// produced: for a nested rand join rule those are the wrappers
// CollectRandJoinSteps built around its operands, and the wrapper is what
// SlotForAppearance is given to look up.
RuleValueCapture BuildStepValueCapture(const Stmt* stmt,
                                       const std::vector<const RsProd*>& steps,
                                       SimContext& ctx) {
  RuleValueCapture cap;
  for (const auto* step : steps) {
    CountRuleProductions(stmt, *step, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

// §18.17.7: the implicit variable this appearance of a production writes. An
// appearance the rule recorded no ordinal for writes none: the top-level
// production the randsequence statement names stands in no rule, and a
// production that returns no value declares no variable to write.
RuleProductionSlot SlotForAppearance(const RuleValueCapture* cap,
                                     const RsProductionItem& call,
                                     std::string_view name) {
  if (cap == nullptr) return RuleProductionSlot{name, 0, 0};
  auto ord = cap->ordinal.find(&call);
  if (ord == cap->ordinal.end()) return RuleProductionSlot{name, 0, 0};
  auto total = cap->total.find(name);
  return RuleProductionSlot{name, ord->second,
                            total == cap->total.end() ? 1 : total->second};
}

// §18.17.7: create the implicit variable that holds a generated production's
// return value. A production named more than once in the rule writes the
// idx-th element of its 1..N array, whose name is built at run time and so must
// be interned in the arena (the scope map keys on a stable string_view); a
// production named once writes the scalar named after the production. The name
// the variable was created under is reported through `created_name`; it
// outlives the call in both forms, so a caller that has to name the variable
// again does not have to rebuild the name.
static Variable* CreateRuleProductionVariable(const RuleProductionSlot& slot,
                                              uint32_t width, SimContext& ctx,
                                              Arena& arena,
                                              std::string_view* created_name) {
  if (slot.total > 1) {
    auto name = std::string(slot.name) + "[" + std::to_string(slot.idx) + "]";
    const std::string& interned = *arena.Create<std::string>(std::move(name));
    *created_name = interned;
    return ctx.CreateLocalVariable(interned, width);
  }
  *created_name = slot.name;
  return ctx.CreateLocalVariable(slot.name, width);
}

// §18.17.7: store one generated production's return value into its implicit
// variable, at the moment it is generated so that a code block written to its
// right observes the value and one written to its left does not.
void StoreRuleProductionValue(const RuleProductionSlot& slot,
                              const RsProduction* child,
                              const Logic4Vec& ret_value, SimContext& ctx,
                              Arena& arena) {
  uint32_t w = EvalTypeWidth(child->return_type);
  if (w == 0) w = ret_value.width;
  // §6.16: a string is as wide as the characters it holds, so a string
  // production that returned nothing leaves the empty string and not 32 bits
  // of zero. Every other return type EvalTypeWidth gives no width to keeps the
  // 32-bit carrier.
  if (w == 0 && !ProductionReturnsString(child)) w = 32;
  std::string_view created_name;
  Variable* var =
      CreateRuleProductionVariable(slot, w, ctx, arena, &created_name);
  var->value = ret_value;
  // §18.17.7 gives the implicit variable the production's return type, and
  // what reads a string reads SimContext::IsStringVariable rather than the
  // width, so register the name the variable was created under. The registry
  // keys on a string_view it never erases, and both names
  // CreateRuleProductionVariable reports outlive this call.
  if (ProductionReturnsString(child)) ctx.RegisterStringVariable(created_name);
}

}  // namespace delta
