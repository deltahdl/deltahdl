#include <cmath>
#include <format>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" || key == "time" ||
         key == "realtime" || key == "string";
}

static bool IsArrayPatternSpecial(const Expr* init) {
  if (init->repeat_count) return true;
  if (init->elements.size() == 1 &&
      init->elements[0]->kind == ExprKind::kReplicate)
    return true;
  return !init->pattern_keys.empty();
}

uint32_t ExtractLiteralWidth(std::string_view text) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      char c = text[i];
      if (c >= '0' && c <= '9') w = w * 10 + (c - '0');
    }
    if (w > 0) return w;
  }
  return 32;
}

std::optional<int64_t> ComputeDimSize(const Expr* dim) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs);
    auto right = ConstEvalInt(dim->rhs);
    if (left && right) return std::abs(*left - *right) + 1;
    return std::nullopt;
  }
  return ConstEvalInt(dim);
}

// What two array pattern keys are the same key by. §10.9's array keys are
// constant expressions, so what a key names is its value: `3` and `N-1` with N
// of 4 name the element between them once, not twice. A key that does not fold
// here is answered for by how it was written, which still tells apart the two
// halves of a key written the same way twice. Nothing for a key that neither
// folds nor was written as a single name or literal -- there is no ground to
// call two of those the same, and calling them so would report every pair of
// them as a duplicate.
static std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key) {
  auto value = ConstEvalInt(key);
  if (value) return std::to_string(*value);
  if (key->text.empty()) return std::nullopt;
  return std::string(key->text);
}

static void CheckArrayPatternDuplicateIndices(const Expr* init, SourceLoc loc,
                                              DiagEngine& diag) {
  if (init->pattern_keys.empty()) return;
  std::unordered_set<std::string> seen;
  for (const auto* key : init->pattern_keys) {
    if (key->text == "default" || IsTypeKeyword(key->text)) continue;
    auto identity = ArrayPatternKeyIdentity(key);
    if (!identity) continue;
    if (!seen.insert(*identity).second) {
      diag.Error(
          loc,
          std::format("duplicate index key '{}' in array pattern", *identity),
          Subclause("10.9.1"));
    }
  }
}

static void CheckArrayPatternCoverage(const ModuleItem* item, SourceLoc loc,
                                      DiagEngine& diag) {
  if (item->init_expr->pattern_keys.empty()) return;
  if (item->unpacked_dims.empty()) return;
  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;
  auto dim_size = ComputeDimSize(dim);
  if (!dim_size) return;

  bool has_default = false;
  bool has_type_key = false;
  std::unordered_set<std::string> index_keys;
  // Keys with no identity are counted rather than collected. Each one is still
  // a key, and leaving them out would read a pattern whose keys the elaborator
  // cannot fold as covering fewer elements than it was written for.
  int64_t unidentified_keys = 0;
  for (const auto* key : item->init_expr->pattern_keys) {
    if (key->text == "default") {
      has_default = true;
    } else if (IsTypeKeyword(key->text)) {
      has_type_key = true;
    } else if (auto identity = ArrayPatternKeyIdentity(key)) {
      index_keys.insert(*identity);
    } else {
      ++unidentified_keys;
    }
  }
  if (has_default || has_type_key) return;
  if (static_cast<int64_t>(index_keys.size()) + unidentified_keys < *dim_size) {
    diag.Error(loc, "keyed array pattern does not cover all elements",
               Subclause("10.9.1"));
  }
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (IsArrayPatternSpecial(item->init_expr)) {
    CheckArrayPatternDuplicateIndices(item->init_expr, item->loc, diag_);
    CheckArrayPatternCoverage(item, item->loc, diag_);
    return;
  }

  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;
  auto dim_size = ComputeDimSize(dim);
  if (!dim_size) return;

  auto count = static_cast<int64_t>(item->init_expr->elements.size());
  if (count != *dim_size) {
    diag_.Error(item->loc,
                std::format("assignment pattern has {} elements, but array "
                            "dimension requires {}",
                            count, *dim_size),
                Subclause("10.9.1"));
  }
}

static void CheckPatternCoverage(
    const ModuleItem* item, const std::vector<StructMember>& members,
    const std::unordered_set<std::string_view>& seen, DiagEngine& diag) {
  for (const auto& m : members) {
    if (!seen.count(m.name)) {
      diag.Error(
          item->loc,
          std::format("member '{}' not covered by assignment pattern", m.name),
          Subclause("10.9.2"));
      break;
    }
  }
}

static void CheckPatternKeys(const ModuleItem* item,
                             const std::vector<StructMember>& members,
                             DiagEngine& diag) {
  std::unordered_set<std::string_view> member_names;
  for (const auto& m : members) member_names.insert(m.name);
  std::unordered_set<std::string_view> seen;
  bool has_default = false;
  bool has_type_key = false;
  // §10.9: `structure_pattern_key ::= member_identifier |
  // assignment_pattern_key`, so every key of a structure pattern is a name --
  // a member's, `default`, or a simple type -- and the key's text is that name.
  for (const auto* key_expr : item->init_expr->pattern_keys) {
    auto key = key_expr->text;
    if (key == "default") {
      has_default = true;
      continue;
    }
    if (IsTypeKeyword(key)) {
      has_type_key = true;
      continue;
    }
    if (!member_names.count(key)) {
      diag.Error(item->loc,
                 std::format("'{}' is not a member of the struct", key),
                 Subclause("10.9.2"));
    }
    if (!seen.insert(key).second) {
      diag.Error(item->loc,
                 std::format("duplicate member key '{}' in pattern", key),
                 Subclause("10.9.2"));
    }
  }

  if (!has_default && !has_type_key) {
    CheckPatternCoverage(item, members, seen, diag);
  }
}

void Elaborator::ValidateStructInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;

  const std::vector<StructMember>* members = nullptr;
  if (!item->data_type.struct_members.empty()) {
    members = &item->data_type.struct_members;
  } else if (item->data_type.kind == DataTypeKind::kNamed) {
    auto td = typedefs_.find(item->data_type.type_name);
    if (td != typedefs_.end() && !td->second.struct_members.empty())
      members = &td->second.struct_members;
  }
  if (!members) return;

  if (item->init_expr->pattern_keys.empty()) {
    bool is_replication =
        item->init_expr->repeat_count ||
        (item->init_expr->elements.size() == 1 &&
         item->init_expr->elements[0]->kind == ExprKind::kReplicate);
    if (is_replication) return;
    if (item->init_expr->elements.size() != members->size()) {
      diag_.Error(
          item->loc,
          std::format("positional struct pattern has {} elements, "
                      "but struct has {} members",
                      item->init_expr->elements.size(), members->size()),
          Subclause("10.9.2"));
    }
    return;
  }

  CheckPatternKeys(item, *members, diag_);
}

std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

std::string_view LhsBaseName(const Expr* e) {
  while (e) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
      e = e->base;
      continue;
    }
    break;
  }
  return {};
}

// §10.4.2 forbids a nonblocking assignment to an element of a dynamically sized
// array variable -- dynamic arrays, queues, and associative arrays all qualify
// because an element's storage can move as the collection is resized between
// the schedule and update steps. `dynsized_names` therefore carries all three
// kinds and gates the nonblocking branch, while `dyn_names` (dynamic arrays
// only) preserves the existing procedural-continuous-assignment diagnostic.
void CheckNbaDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    const std::unordered_set<std::string_view>& dynsized_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && s->lhs->kind == ExprKind::kSelect) {
    auto name = LhsBaseName(s->lhs);
    if (!name.empty() && s->kind == StmtKind::kNonblockingAssign &&
        dynsized_names.count(name) != 0) {
      diag.Error(s->range.start,
                 "nonblocking assignment to element of dynamically sized array",
                 Subclause("6.21"));
    } else if (!name.empty() && dyn_names.count(name) != 0 &&
               (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign)) {
      diag.Error(s->range.start,
                 "procedural continuous assignment to element of "
                 "dynamic array",
                 Subclause("6.21"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckNbaDynamicArrayTarget(sub, dyn_names, dynsized_names, diag);
  });
}

static void CollectLhsBaseNames(
    const Expr* e, SourceLoc loc,
    std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) CollectLhsBaseNames(elem, loc, out);
    return;
  }
  auto name = LhsBaseName(e);
  if (!name.empty()) out.emplace(name, loc);
}

// Records the variable each blocking or nonblocking assignment writes, for
// §6.5's rule that "it shall be an error to have multiple continuous
// assignments or a mixture of procedural and continuous assignments writing to
// any term in the expansion of the longest static prefix of a variable", and
// for §6.5's other rule that a net cannot be the target of a procedural
// assignment. Both tests read sets that are complete only after every item has
// been walked, so this only collects; Elaborator::ValidateMixedAssignments and
// Elaborator::ValidateProceduralNetAssign report.
//
// The statement position an assignment stands in decides neither rule, so this
// recurses through ForEachChildStmt, which holds the list of every field of
// Stmt that carries a statement.
void CollectProcTargets(const Stmt* s,
                        std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CollectLhsBaseNames(s->lhs, s->range.start, out);
  }
  ForEachChildStmt(s,
                   [&out](const Stmt* sub) { CollectProcTargets(sub, out); });
}

// Records the variable each force or release statement names, for §10.6.2's
// rule that neither "shall be applied to a variable that is being assigned by
// a mixture of continuous and procedural assignments". The rule reads sets that
// are complete only after every item has been walked, so the test itself is
// left to Elaborator::ValidateMixedAssignments and this only collects. Uses the
// same CollectLhsBaseNames as CollectProcTargets, which descends a
// concatenation, because §10.6.2 admits "a concatenation of these" as a force
// target and the rule holds of each operand. Recurses through ForEachChildStmt
// for the reason CollectProcTargets above does: where a force or release is
// written decides nothing about the rule.
void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease) {
    CollectLhsBaseNames(s->lhs, s->range.start, out);
  }
  ForEachChildStmt(
      s, [&out](const Stmt* sub) { CollectForceReleaseTargets(sub, out); });
}

void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease ||
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kDeassign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && interconnect_names.count(name)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in procedural "
                 "continuous assignment",
                 Subclause("6.6.8"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProcContAssign(sub, interconnect_names, diag);
  });
}

// §6.6.8: an interconnect net is typeless/generic and shall not be used in any
// procedural context, nor in any expression other than a net_lvalue whose nets
// are all interconnect. Procedural-assignment targets are already rejected (by
// the net-target rule and CheckInterconnectProcContAssign); this closes the
// read side by flagging any interconnect net appearing in a procedural
// statement's read expressions — an assignment RHS, an if/case/loop condition,
// a case pattern, a delay, an assertion expression, or a call argument.
void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  const Expr* reads[] = {s->rhs,      s->condition,          s->for_cond,
                         s->delay,    s->cycle_delay,        s->expr,
                         s->var_init, s->repeat_event_count, s->assert_expr};
  for (const Expr* e : reads) {
    if (ExprUsesInterconnect(e, interconnect_names)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in a procedural expression",
                 Subclause("6.6.8"));
      break;
    }
  }
  for (auto& ci : s->case_items)
    for (const auto* p : ci.patterns)
      if (ExprUsesInterconnect(p, interconnect_names)) {
        diag.Error(s->range.start,
                   "interconnect net cannot be used in a procedural expression",
                   Subclause("6.6.8"));
        break;
      }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProceduralRead(sub, interconnect_names, diag);
  });
}

// §10.6.1: the LHS of an assign statement shall be a singular variable
// reference or a concatenation of variables, and shall not be a bit-select or a
// part-select of a variable. Because the concatenation must be one *of
// variables*, a bit-select or part-select element inside the concatenation is
// equally illegal, so the check descends through concatenations rather than
// only inspecting the top-level lvalue.
static bool ProceduralAssignLhsHasSelect(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSelect) return true;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements)
      if (ProceduralAssignLhsHasSelect(elem)) return true;
  }
  return false;
}

void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kAssign && ProceduralAssignLhsHasSelect(s->lhs)) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }
  ForEachChildStmt(
      s, [&diag](const Stmt* sub) { CheckProceduralAssignLhs(sub, diag); });
}

static void CheckForceLhsOperand(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements)
      CheckForceLhsOperand(el, net_names, nettype_net_names, loc, diag);
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    auto base_name = LhsBaseName(e);
    if (base_name.empty()) return;
    if (nettype_net_names.count(base_name) != 0) {
      diag.Error(loc,
                 "bit-select or part-select of a net with a user-defined "
                 "nettype is not a legal force LHS",
                 Subclause("10.6.2"));
    } else if (net_names.count(base_name) == 0) {
      diag.Error(loc,
                 "bit-select or part-select of a variable is not a "
                 "legal force LHS",
                 Subclause("10.6.2"));
    }
  }
}

// Reports §10.6.2's rule on what a force statement may name, at every statement
// position a force can stand in, which is what ForEachChildStmt enumerates.
void CheckForceLhs(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce && s->lhs) {
    CheckForceLhsOperand(s->lhs, net_names, nettype_net_names, s->range.start,
                         diag);
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckForceLhs(sub, net_names, nettype_net_names, diag);
  });
}

// True when any expression of `list` reads one of the named nets.
static bool AnyExprUsesInterconnect(
    const std::vector<Expr*>& list,
    const std::unordered_set<std::string_view>& names) {
  for (auto* sub : list)
    if (ExprUsesInterconnect(sub, names)) return true;
  return false;
}

bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return names.count(e->text) > 0;
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end}) {
    if (ExprUsesInterconnect(sub, names)) return true;
  }
  return AnyExprUsesInterconnect(e->args, names) ||
         AnyExprUsesInterconnect(e->elements, names);
}

bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

using NameSet = std::unordered_set<std::string_view>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                const SelectOperands& operands,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  const bool kIsRealVar = !name.empty() && operands.variables.count(name) != 0;
  const bool kIsRealParam =
      !name.empty() && operands.parameters.count(name) != 0;
  if (kIsRealVar || kIsRealParam) {
    // §11.5.1: "A bit-select or part-select of a scalar, or of a real variable
    // or real parameter, shall be illegal." The sentence names two constructs
    // and two real operands, so the report names the construct that was written
    // and the operand it was written on. A select node carries `index_end` for
    // `[m:l]` and `is_part_select_plus` or `is_part_select_minus` for `[b +:
    // w]` and `[b -: w]`, the same three fields CheckIndexedPartSelectWidthNode
    // reads; a node with none of them set is a bit-select.
    //
    // The two name sets are asked rather than the declared type of the operand,
    // because a real declared with an unpacked dimension is in neither set:
    // §11.5.2 makes indexing it an array element select, so
    // `real arr[4]; v = arr[i];` reads an element and is legal.
    const bool kIsBitSelect =
        !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
    const char* const kConstruct = kIsBitSelect ? "bit-select" : "part-select";
    const char* const kOperand =
        kIsRealVar ? "real variable" : "real parameter";
    diag.Error(e->range.start,
               std::format("{} of a {} is illegal", kConstruct, kOperand),
               Subclause("11.5.1"));
    // Returning here leaves the index check below unreached for this node, so
    // `real a; real i; assign b = a[i];` draws the operand report alone. That
    // is deliberate: the operand breach already makes the whole select illegal
    // under the sentence quoted above, and one construct drawing one report is
    // what this check exists to do.
    return;
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start, "real type used as index is illegal",
               Subclause("11.5.1"));
  }
}

// §11.5.2: the name a chain of selects is written on, and how many addresses
// the chain carries. Parser::ParseSelectExpr in src/parser/expr_parser.cpp
// builds one ExprKind::kSelect node per bracketed address, so `arr[i][0]` is
// two nodes with the inner one standing as the outer one's `base`.
struct SelectChain {
  std::string_view name;
  size_t addresses = 0;
};

static SelectChain ResolveSelectChain(const Expr* e) {
  SelectChain chain;
  const Expr* n = e;
  while (n && n->kind == ExprKind::kSelect) {
    ++chain.addresses;
    n = n->base;
  }
  if (n && n->kind == ExprKind::kIdentifier) chain.name = n->text;
  return chain;
}

// §11.5.1 reached through §11.5.2: report an address written one past the
// dimensions of the declaration the chain stands on. §11.5.2 says "the desired
// word shall first be selected by supplying an address for each dimension" and
// that the select which follows is "addressed in the same manner as net and
// variable bit-selects and part-selects (see 11.5.1)", so `real arr[4];
// v = arr[i][0];` is the bit-select of a real that sentence bars, and
// `logic [7:0] mem[4]; v = mem[i][0];` is the legal case the same sentence
// exists to permit.
static void CheckElementSelectNode(const Expr* e, const SelectShapeMap& shapes,
                                   DiagEngine& diag) {
  // Only a chain of two or more addresses is judged here. A select carrying one
  // address is the case CheckRealSelectNode and CheckScalarSelectNode already
  // report from the name sets, and judging it here as well would make one
  // breach draw two reports.
  if (!e->base || e->base->kind != ExprKind::kSelect) return;
  SelectChain chain = ResolveSelectChain(e);
  if (chain.name.empty()) return;
  auto it = shapes.find(chain.name);
  if (it == shapes.end()) return;
  // Exactly the first address past the last dimension is reported. A longer
  // chain addresses bits of that bit, which this one report already stands for.
  if (chain.addresses != it->second.addressable_dims + 1) return;
  const bool kIsBitSelect =
      !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
  if (it->second.element_is_real) {
    diag.Error(e->range.start,
               std::format("{} of a real variable is illegal",
                           kIsBitSelect ? "bit-select" : "part-select"),
               Subclause("11.5.1"));
    return;
  }
  if (it->second.element_is_scalar) {
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
  }
}

void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, operands, diag);
    // The element-select case rides this walk rather than one of its own,
    // because it is judged at the same nodes and both alternatives of
    // §11.5.1's sentence are reported from here.
    CheckElementSelectNode(e, operands.shapes, diag);
  }
  ForEachExprChild(e, [&](const Expr* child) {
    CheckRealSelect(child, types, operands, diag);
  });
}

static void CheckScalarSelectNode(const Expr* e, const NameSet& scalars,
                                  DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (name.empty()) return;
  if (scalars.count(name) != 0)
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
}

void CheckScalarSelect(const Expr* e, const NameSet& scalars,
                       DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckScalarSelectNode(e, scalars, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckScalarSelect(child, scalars, diag); });
}

static void CheckIndexedPartSelectWidthNode(const Expr* e,
                                            const ScopeMap& scope,
                                            DiagEngine& diag) {
  if (!e->index_end) return;
  if (!e->is_part_select_plus && !e->is_part_select_minus) return;
  // §11.5.1: the width is a constant expression, which per §11.2.1 may be a
  // parameter/localparam reference. Evaluate it in the module's parameter scope
  // so `x[i +: WIDTH]` resolves rather than being rejected as non-constant.
  auto width = ConstEvalInt(e->index_end, scope);
  if (!width.has_value()) {
    diag.Error(e->range.start,
               "indexed part-select width must be a constant expression",
               Subclause("11.5.1"));
    return;
  }
  // §11.5.1 requires the width of an indexed part-select to be positive.
  if (*width <= 0)
    diag.Error(e->range.start,
               "indexed part-select width must be a positive constant",
               Subclause("11.5.1"));
}

void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckIndexedPartSelectWidthNode(e, scope, diag);
  ForEachExprChild(e, [&](const Expr* child) {
    CheckIndexedPartSelectWidth(child, scope, diag);
  });
}

void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag) {
  if (!s) return;
  CheckScalarSelect(s->lhs, scalars, diag);
  CheckScalarSelect(s->rhs, scalars, diag);
  CheckScalarSelect(s->expr, scalars, diag);
  CheckScalarSelect(s->condition, scalars, diag);
  CheckScalarSelect(s->for_cond, scalars, diag);
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CheckScalarSelectStmt(sub, scalars, diag); });
}

// §11.5.1 applies to a select written in a procedural statement exactly as it
// applies to one written on a continuous assignment. The real-operand check
// reaches every statement position CheckScalarSelectStmt reaches because both
// recurse through ForEachChildStmt.
void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag) {
  if (!s) return;
  CheckRealSelect(s->lhs, types, operands, diag);
  CheckRealSelect(s->rhs, types, operands, diag);
  CheckRealSelect(s->expr, types, operands, diag);
  CheckRealSelect(s->condition, types, operands, diag);
  CheckRealSelect(s->for_cond, types, operands, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckRealSelectStmt(sub, types, operands, diag);
  });
}

void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag) {
  if (!s) return;
  CheckIndexedPartSelectWidth(s->lhs, scope, diag);
  CheckIndexedPartSelectWidth(s->rhs, scope, diag);
  CheckIndexedPartSelectWidth(s->expr, scope, diag);
  CheckIndexedPartSelectWidth(s->condition, scope, diag);
  CheckIndexedPartSelectWidth(s->for_cond, scope, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckIndexedPartSelectWidthStmt(sub, scope, diag);
  });
}

bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  return AnyExprChild(
      e, [name](const Expr* child) { return ExprContainsIdent(child, name); });
}

NettypeResolutionRule ValidateNettypeResolutionFunction(
    const NettypeResolutionSig& sig) {
  // The requirements §6.6.7 states, one test each, returned in the order the
  // clause writes them: "shall be a function with a return type of T and a
  // single input argument whose type is a dynamic array of elements of type T.
  // A resolution function shall be automatic (or preserve no state
  // information)". The first one broken is what the caller reports, so a
  // signature breaking several names the first rather than all of them.
  if (!sig.return_type_matches_nettype)
    return NettypeResolutionRule::kReturnType;
  if (!sig.single_input_argument) return NettypeResolutionRule::kArgumentCount;
  if (!sig.argument_is_input) return NettypeResolutionRule::kArgumentDirection;
  if (!sig.argument_is_dynamic_array)
    return NettypeResolutionRule::kArgumentIsDynamicArray;
  if (!sig.argument_element_type_matches)
    return NettypeResolutionRule::kArgumentElementType;
  if (!sig.is_automatic) return NettypeResolutionRule::kAutomaticLifetime;
  // A class method is admissible only when it is static, because the resolution
  // call occurs with no class object involved.
  if (sig.is_class_method && !sig.is_static_method)
    return NettypeResolutionRule::kClassStaticMethod;
  return NettypeResolutionRule::kConforming;
}

}  // namespace delta
