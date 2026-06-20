#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ProcessPendingGenerate(ModuleItem* item, RtlirModule* mod) {
  auto scope = BuildParamScope(mod);
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      ElaborateGenerateIf(item, mod, scope);
      break;
    case ModuleItemKind::kGenerateCase:
      ElaborateGenerateCase(item, mod, scope);
      break;
    case ModuleItemKind::kGenerateFor:
      ElaborateGenerateFor(item, mod, scope);
      break;
    default:
      break;
  }
}

void Elaborator::ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                                        RtlirModule* mod,
                                        const ScopeMap& scope) {
  for (auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kGenerateIf:
        ElaborateGenerateIf(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateCase:
        ElaborateGenerateCase(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateFor:
        ElaborateGenerateFor(item, mod, scope);
        break;
      default:
        ElaborateItem(item, mod);
        break;
    }
  }
}

void Elaborator::ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                                     const ScopeMap& scope) {
  auto cond = ConstEvalInt(item->gen_cond, scope);
  if (!cond) {
    diag_.Warning(item->loc, "generate-if condition is not constant");
    return;
  }
  if (*cond) {
    ElaborateGenerateItems(item->gen_body, mod, scope);
  } else if (item->gen_else) {
    ElaborateGenerateItems(item->gen_else->gen_body, mod, scope);
  }
}

static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  for (const auto* pat : patterns) {
    auto val = ConstEvalInt(pat, scope);
    if (val && *val == selector) return true;
  }
  return false;
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  auto selector = ConstEvalInt(item->gen_cond, scope);
  if (!selector) {
    diag_.Warning(item->loc, "generate-case selector is not constant");
    return;
  }
  const std::vector<ModuleItem*>* default_body = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_body = &ci.body;
      continue;
    }
    if (MatchesCasePattern(ci.patterns, *selector, scope)) {
      ElaborateGenerateItems(ci.body, mod, scope);
      return;
    }
  }
  if (default_body) {
    ElaborateGenerateItems(*default_body, mod, scope);
  }
}

static bool IsGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf ||
         k == ModuleItemKind::kGenerateFor ||
         k == ModuleItemKind::kGenerateCase;
}

void Elaborator::AssignGenerateBlockNames(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> used;
  for (const auto& port : decl->ports) used.insert(port.name);
  for (const auto& p : decl->params) used.insert(p.first);
  for (auto* it : decl->items) {
    if (!it->name.empty()) used.insert(it->name);
  }

  int64_t n = 0;
  for (auto* it : decl->items) {
    if (!IsGenerateConstruct(it->kind)) continue;
    ++n;
    if (!it->name.empty()) continue;
    std::string digits = std::to_string(n);
    std::string candidate = "genblk" + digits;
    while (used.count(candidate)) {
      digits = "0" + digits;
      candidate = "genblk" + digits;
    }
    auto* buf = arena_.AllocString(candidate.c_str(), candidate.size());
    it->name = std::string_view(buf, candidate.size());
    used.insert(it->name);
  }
}

// §27.5: gather the block names introduced by the alternatives of a single
// generate construct. An if-generate contributes its then-block name and,
// recursively, the names of every else / else-if alternative; a case-generate
// contributes the label of each case item (including default); a loop generate
// contributes its array name. Names are collected into a set so that the same
// name labelling more than one alternative of one conditional construct counts
// only once -- at most one alternative is ever instantiated, so reusing a name
// across the alternatives of a single conditional construct is permitted.
static void CollectGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items) {
        if (!ci.label.empty()) out.insert(ci.label);
      }
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

// §27.5: enforce the naming rules for conditional generate constructs. A named
// generate block shares the enclosing scope's namespace, so the name of a block
// in an if-generate or case-generate must not also name another declaration in
// that scope, nor a generate block belonging to a different generate construct
// in the same scope. The check looks at every alternative of the construct,
// independent of which one (if any) elaboration selects for instantiation, so a
// collision is reported even when the offending block is not instantiated.
// Reusing a name across the alternatives of one conditional construct is left
// untouched: those names are deduplicated per construct, so only one will be
// counted.
void Elaborator::CheckConditionalGenerateNaming(const ModuleDecl* decl) {
  // Names of ordinary declarations in this scope: ports, parameters, and the
  // named module items that are not themselves generate constructs.
  std::unordered_set<std::string_view> decl_names;
  for (const auto& port : decl->ports)
    if (!port.name.empty()) decl_names.insert(port.name);
  for (const auto& p : decl->params)
    if (!p.first.empty()) decl_names.insert(p.first);
  for (const auto* item : decl->items) {
    if (IsGenerateConstruct(item->kind)) continue;
    if (!item->name.empty()) decl_names.insert(item->name);
    if (!item->inst_name.empty()) decl_names.insert(item->inst_name);
    if (!item->gate_inst_name.empty()) decl_names.insert(item->gate_inst_name);
  }

  // How many distinct generate constructs in this scope declare a block of each
  // name. A name claimed by more than one construct violates the rule against
  // sharing a block name across conditional or loop generate constructs.
  std::unordered_map<std::string_view, int> construct_uses;
  for (const auto* item : decl->items) {
    if (!IsGenerateConstruct(item->kind)) continue;
    std::unordered_set<std::string_view> names;
    CollectGenerateBlockNames(item, names);
    for (auto n : names) ++construct_uses[n];
  }

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGenerateIf &&
        item->kind != ModuleItemKind::kGenerateCase) {
      continue;
    }
    std::unordered_set<std::string_view> names;
    CollectGenerateBlockNames(item, names);
    for (auto n : names) {
      if (decl_names.count(n)) {
        diag_.Error(item->loc,
                    std::format("generate block '{}' conflicts with another "
                                "declaration in the same scope",
                                n));
      } else if (construct_uses[n] > 1) {
        diag_.Error(item->loc,
                    std::format("generate block '{}' has the same name as a "
                                "generate block in another generate construct "
                                "in the same scope",
                                n));
      }
    }
  }
}

static constexpr int64_t kMaxGenerateIterations = 65536;

static bool ExprReferencesName(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprReferencesName(e->lhs, name)) return true;
  if (ExprReferencesName(e->rhs, name)) return true;
  for (const auto* a : e->args) {
    if (ExprReferencesName(a, name)) return true;
  }
  return false;
}

static std::string_view StepLhsName(const Stmt* step) {
  if (!step) return {};
  if (step->lhs && step->lhs->kind == ExprKind::kIdentifier) {
    return step->lhs->text;
  }
  if (step->expr) {
    const auto* e = step->expr;
    if ((e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
        e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
      return e->lhs->text;
    }
  }
  return {};
}

// §27.4: a genvar value with any bit set to x or z is illegal during loop
// evaluation. Only a based integer literal whose digits include x, z, or ?
// can introduce such a bit, so scan the genvar's init/step expression for
// one (recursing through operands).
static bool ExprHasXZLiteral(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIntegerLiteral) {
    std::string_view text = e->text;
    if (text.find('\'') == std::string_view::npos) return false;
    for (char c : text) {
      if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
    }
    return false;
  }
  return ExprHasXZLiteral(e->lhs) || ExprHasXZLiteral(e->rhs);
}

void Elaborator::ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                                      const ScopeMap& scope) {
  if (!item->gen_init || !item->gen_init->lhs) {
    diag_.Warning(item->loc, "malformed generate-for initializer");
    return;
  }
  auto genvar_name = item->gen_init->lhs->text;

  if (ExprReferencesName(item->gen_init->rhs, genvar_name)) {
    diag_.Error(item->loc,
                "generate-for init shall not reference the loop index on the "
                "right-hand side");
    return;
  }

  auto step_lhs = StepLhsName(item->gen_step);
  if (!step_lhs.empty() && step_lhs != genvar_name) {
    diag_.Error(item->loc,
                "generate-for init and step shall assign to the same genvar");
    return;
  }

  // §27.4: it shall be an error if any bit of the genvar is set to x or z
  // during evaluation. An x/z initialization value triggers a dedicated
  // error rather than the generic non-constant warning.
  if (ExprHasXZLiteral(item->gen_init->rhs)) {
    diag_.Error(item->loc,
                "generate-for genvar shall not have any bit set to x or z "
                "during evaluation");
    return;
  }

  // §27.4: a named loop generate block declares an array of generate block
  // instances, and it shall be an error if that array's name collides with any
  // other declaration in the enclosing scope, including another generate block
  // instance array. The array counts as declared even when the loop yields no
  // instances, so this check runs before the iteration count is known. Loop
  // generate arrays are an error on conflict (unlike conditional generate
  // blocks, whose naming rules differ), so the loop path enforces it directly
  // rather than through the shared label collector.
  if (!item->name.empty()) {
    if (IsNameDeclared(item->name, mod) ||
        !declared_names_.insert(item->name).second) {
      diag_.Error(item->loc,
                  std::format("generate block array '{}' conflicts with an "
                              "existing declaration in the same scope",
                              item->name));
      return;
    }
  }

  auto init_val = ConstEvalInt(item->gen_init->rhs, scope);
  if (!init_val) {
    diag_.Warning(item->loc, "generate-for init is not constant");
    return;
  }

  ScopeMap loop_scope = scope;
  loop_scope[genvar_name] = *init_val;
  std::string saved_prefix = gen_prefix_;

  std::unordered_set<int64_t> seen_values;

  int64_t iter = 0;
  for (; iter < kMaxGenerateIterations; ++iter) {
    auto cond = ConstEvalInt(item->gen_cond, loop_scope);
    if (!cond || !*cond) break;

    if (!seen_values.insert(loop_scope[genvar_name]).second) {
      diag_.Error(item->loc,
                  "generate-for genvar value is repeated during evaluation");
      gen_prefix_ = saved_prefix;
      return;
    }

    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, genvar_name,
                              loop_scope[genvar_name]);
    ElaborateGenerateItems(item->gen_body, mod, loop_scope);

    // §27.4: the x/z prohibition holds as the loop advances; a step that
    // drives the genvar to an x or z bit is an error, not a silent stop.
    if (ExprHasXZLiteral(item->gen_step->rhs) ||
        ExprHasXZLiteral(item->gen_step->expr)) {
      diag_.Error(item->loc,
                  "generate-for genvar shall not have any bit set to x or z "
                  "during evaluation");
      gen_prefix_ = saved_prefix;
      return;
    }

    std::optional<int64_t> next;
    if (item->gen_step->rhs) {
      next = ConstEvalInt(item->gen_step->rhs, loop_scope);
    } else if (item->gen_step->expr) {
      auto* e = item->gen_step->expr;
      if ((e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
          e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
        auto it = loop_scope.find(e->lhs->text);
        if (it != loop_scope.end()) {
          if (e->op == TokenKind::kPlusPlus)
            next = it->second + 1;
          else if (e->op == TokenKind::kMinusMinus)
            next = it->second - 1;
        }
      }
    }
    if (!next) break;
    loop_scope[genvar_name] = *next;
  }

  if (iter == kMaxGenerateIterations) {
    diag_.Error(item->loc, "generate-for loop did not terminate");
  }

  gen_prefix_ = saved_prefix;
}

}  // namespace delta
