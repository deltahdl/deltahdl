#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/let_construct.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateDpiImport(const ModuleItem* item) {
  // §35.5.2's restrictions apply only to imports declared pure.
  if (!item->dpi_is_pure) return;

  if (item->dpi_is_task) {
    diag_.Error(item->loc, "imported task cannot be declared pure (§35.5.2)");
    return;
  }
  if (item->return_type.kind == DataTypeKind::kVoid) {
    diag_.Error(item->loc,
                "pure imported function must have a non-void return type "
                "(§35.5.2)");
  }

  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kOutput ||
        arg.direction == Direction::kInout) {
      diag_.Error(item->loc,
                  "pure imported function cannot have output or inout "
                  "arguments (§35.5.2)");
      break;
    }
  }
}

namespace {

// §35.5.4: the linkage name is the explicit c_identifier when given, otherwise
// it defaults to the SystemVerilog subroutine name.
std::string_view DpiLinkageName(const ModuleItem* item) {
  return item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
}

// §35.5.4 enumerates the parts of the type signature that must match across
// every declaration sharing one linkage name: return type, argument count,
// per-argument direction and type, plus the pure/context qualifiers and the
// dpi_spec_string itself.
struct DpiSignatureKey {
  DataTypeKind return_type;
  bool is_pure;
  bool is_context;
  bool is_task;
  std::string_view spec_string;
  std::vector<std::pair<Direction, DataTypeKind>> args;
};

DpiSignatureKey BuildDpiSignature(const ModuleItem* item) {
  DpiSignatureKey key;
  key.return_type = item->return_type.kind;
  key.is_pure = item->dpi_is_pure;
  key.is_context = item->dpi_is_context;
  key.is_task = item->dpi_is_task;
  key.spec_string = item->dpi_spec_string;
  key.args.reserve(item->func_args.size());
  for (const auto& arg : item->func_args) {
    key.args.emplace_back(arg.direction, arg.data_type.kind);
  }
  return key;
}

bool DpiSignaturesMatch(const DpiSignatureKey& a, const DpiSignatureKey& b) {
  return a.return_type == b.return_type && a.is_pure == b.is_pure &&
         a.is_context == b.is_context && a.is_task == b.is_task &&
         a.spec_string == b.spec_string && a.args == b.args;
}

// §35.4: an export declaration borrows its type signature from the
// SystemVerilog function or task it names. The parts that matter for
// equivalence — the return type, the function-vs-task distinction, and
// each formal argument's direction and type kind — are extracted here so
// that two exports sharing one linkage identifier across scopes can be
// compared without paying attention to identifiers, default values, or
// other non-signature details.
struct DpiExportSignature {
  DataTypeKind return_type;
  bool is_task;
  std::vector<std::pair<Direction, DataTypeKind>> args;
  bool operator==(const DpiExportSignature&) const = default;
};

// §35.5.5: "The same restrictions apply for the result types of exported
// functions." An exported function's result is therefore limited to the same
// small-value set imposed on imported function results: void, the C-compatible
// scalar integer/real types, chandle, string, and scalar bit/logic. A native
// function whose return type is omitted carries an implicit single-bit logic
// result, which is itself a small value, so the implicit kind is permitted
// here. Named/typedef results are deferred. Wide vector types (integer, time,
// packed bit/logic) and aggregates are rejected.
bool IsPermittedDpiResultType(const DataType& type) {
  switch (type.kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kVoid:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
    case DataTypeKind::kNamed:
      return true;
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return type.packed_dim_left == nullptr && type.extra_packed_dims.empty();
    default:
      return false;
  }
}

DpiExportSignature BuildDpiExportSignature(const ModuleItem* callable) {
  DpiExportSignature key;
  key.return_type = callable->return_type.kind;
  key.is_task = callable->kind == ModuleItemKind::kTaskDecl;
  key.args.reserve(callable->func_args.size());
  for (const auto& arg : callable->func_args) {
    key.args.emplace_back(arg.direction, arg.data_type.kind);
  }
  return key;
}

}  // namespace

void Elaborator::ValidateDpiDeclarations() {
  if (unit_ == nullptr) return;

  std::unordered_map<std::string_view, DpiSignatureKey> signatures;
  std::unordered_map<std::string_view, SourceLoc> first_decl_loc;

  for (const auto* mod : unit_->modules) {
    if (mod == nullptr) continue;

    // §35.5.4: "multiple imports of the same subroutine name into the same
    // scope are forbidden." We treat each module declaration as one scope.
    std::unordered_set<std::string_view> sv_names_in_scope;
    for (const auto* item : mod->items) {
      if (item == nullptr) continue;
      if (item->kind != ModuleItemKind::kDpiImport) continue;
      auto [it, inserted] = sv_names_in_scope.insert(item->name);
      if (!inserted) {
        diag_.Error(
            item->loc,
            std::format("DPI import name '{}' already declared in this scope",
                        item->name));
      }
    }

    for (const auto* item : mod->items) {
      if (item == nullptr) continue;
      // Signature comparison applies to imports only — an export declaration
      // carries no signature in its syntax (the signature comes from the
      // SystemVerilog function being exported).
      if (item->kind != ModuleItemKind::kDpiImport) continue;

      auto link_name = DpiLinkageName(item);
      auto sig = BuildDpiSignature(item);

      auto found = signatures.find(link_name);
      if (found == signatures.end()) {
        signatures.emplace(link_name, std::move(sig));
        first_decl_loc[link_name] = item->loc;
        continue;
      }
      // §35.5.4: "all declarations, regardless of scope, shall have exactly
      // the same type signature." Argument names and defaults may differ.
      if (!DpiSignaturesMatch(found->second, sig)) {
        diag_.Error(
            item->loc,
            std::format(
                "DPI declaration of linkage name '{}' disagrees with the "
                "earlier declaration's type signature",
                link_name));
      }
    }
  }
}

void Elaborator::ValidateDpiGlobalNameSpace() {
  if (unit_ == nullptr) return;

  // §35.4: track the DPI version string ("DPI-C" or the deprecated "DPI")
  // associated with each linkage identifier the first time we see it. Any
  // later declaration sharing that linkage identifier must agree on the
  // version string — the rule applies to imports and exports alike.
  std::unordered_map<std::string_view, std::string_view> link_version;

  // §35.4: track the SystemVerilog signature each export linkage name was
  // first observed under. Subsequent exports of the same linkage name across
  // any scope must agree, since claim 14 requires equivalent type signatures
  // for cross-scope exports sharing one c_identifier.
  std::unordered_map<std::string_view, DpiExportSignature> export_signatures;

  for (const auto* mod : unit_->modules) {
    if (mod == nullptr) continue;

    // Index this module's SystemVerilog function and task declarations by
    // name so each export can look up the routine it names and obtain its
    // signature for the cross-scope equivalence check.
    std::unordered_map<std::string_view, const ModuleItem*> sv_callables;
    for (const auto* item : mod->items) {
      if (item == nullptr) continue;
      if (item->kind == ModuleItemKind::kFunctionDecl ||
          item->kind == ModuleItemKind::kTaskDecl) {
        sv_callables.emplace(item->name, item);
      }
    }

    // §35.4: multiple export declarations with the same c_identifier in the
    // same scope are forbidden. Each module declaration is one scope, so we
    // track the set of export linkage names seen within this module.
    std::unordered_set<std::string_view> export_link_in_scope;

    // §35.7: "Only one export declaration is permitted per SystemVerilog
    // function." Linkage-name deduplication catches the explicit/implicit
    // c_identifier overlap from §35.4, but two exports of the same SV
    // function with distinct c_identifiers would slip past that check.
    // Tracking SV function names per scope catches that case directly.
    std::unordered_set<std::string_view> exported_sv_func_in_scope;

    for (const auto* item : mod->items) {
      if (item == nullptr) continue;
      if (item->kind != ModuleItemKind::kDpiImport &&
          item->kind != ModuleItemKind::kDpiExport) {
        continue;
      }

      auto link_name = DpiLinkageName(item);

      if (item->kind == ModuleItemKind::kDpiExport) {
        auto [_, inserted] = export_link_in_scope.insert(link_name);
        if (!inserted) {
          diag_.Error(
              item->loc,
              std::format("DPI export linkage name '{}' already declared in "
                          "this scope",
                          link_name));
        }

        // §35.7: at most one export per SystemVerilog function in a scope.
        auto [_func, func_inserted] =
            exported_sv_func_in_scope.insert(item->name);
        if (!func_inserted) {
          diag_.Error(
              item->loc,
              std::format("SystemVerilog function '{}' is already exported in "
                          "this scope; only one export declaration per "
                          "function is permitted (§35.7)",
                          item->name));
        }

        auto callable_it = sv_callables.find(item->name);
        if (callable_it == sv_callables.end()) {
          // §35.7: an export declaration is allowed only in the scope where
          // the function being exported is defined. If the scope contains no
          // SystemVerilog function or task with the named identifier, the
          // export has nothing to attach to.
          diag_.Error(
              item->loc,
              std::format("DPI export names '{}', which is not a "
                          "SystemVerilog function or task defined in the "
                          "enclosing scope (§35.7)",
                          item->name));
        } else {
          // §35.7: an exported function adheres to the same restrictions on
          // argument types as imports. The §35.5.4 prohibition on the ref
          // qualifier in a DPI declaration therefore carries through to the
          // exported routine's formal arguments.
          for (const auto& arg : callable_it->second->func_args) {
            if (arg.direction == Direction::kRef) {
              diag_.Error(
                  item->loc,
                  std::format("SystemVerilog function '{}' has a ref argument "
                              "and therefore cannot be exported (§35.7)",
                              item->name));
              break;
            }
          }

          // §35.5.6: it is erroneous for an exported DPI subroutine to declare
          // a formal argument of a dynamic array type. (Unsized "open" array
          // formals are a relaxation reserved for imports under §35.5.6.1;
          // exports get no such allowance.) A dynamic array shows up as an
          // unpacked dimension with no bounds -- the empty-bracket "[]" form,
          // recorded by the parser as a null dimension entry. Queues ("[$]"),
          // associative arrays ("[*]" / "[type]") and fixed-size unpacked
          // arrays all carry a non-null dimension marker, so they are not
          // mistaken for dynamic arrays here.
          for (const auto& arg : callable_it->second->func_args) {
            bool has_dynamic_dim = false;
            for (const Expr* dim : arg.unpacked_dims) {
              if (dim == nullptr) {
                has_dynamic_dim = true;
                break;
              }
            }
            if (has_dynamic_dim) {
              diag_.Error(
                  item->loc,
                  std::format("SystemVerilog function '{}' has a dynamic array "
                              "formal argument and therefore cannot be exported "
                              "for DPI (§35.5.6)",
                              item->name));
              break;
            }
          }

          // §35.5.5: an exported function's result type is subject to the same
          // small-value restriction as an imported function's result. Tasks
          // carry no result, so the check applies only when the exported
          // routine is a function.
          if (callable_it->second->kind == ModuleItemKind::kFunctionDecl &&
              !IsPermittedDpiResultType(callable_it->second->return_type)) {
            diag_.Error(
                item->loc,
                std::format("exported function '{}' has a result type that is "
                            "not permitted for DPI; function results are "
                            "restricted to small values (§35.5.5)",
                            item->name));
          }

          auto sig = BuildDpiExportSignature(callable_it->second);
          auto [sig_it, sig_was_new] =
              export_signatures.emplace(link_name, sig);
          if (!sig_was_new && !(sig_it->second == sig)) {
            diag_.Error(
                item->loc,
                std::format("DPI export linkage name '{}' was previously "
                            "declared with a different type signature; "
                            "exports sharing one linkage name across scopes "
                            "must have equivalent signatures",
                            link_name));
          }
        }
      }

      auto found = link_version.find(link_name);
      if (found == link_version.end()) {
        link_version.emplace(link_name, item->dpi_spec_string);
        continue;
      }
      if (found->second != item->dpi_spec_string) {
        diag_.Error(
            item->loc,
            std::format("DPI linkage name '{}' was previously declared with "
                        "version string \"{}\"; all declarations sharing one "
                        "linkage name must use the same version string",
                        link_name, found->second));
      }
    }
  }
}

void Elaborator::ValidateElabSystemTask(const ModuleItem* item,
                                        const RtlirModule* mod) {
  auto* expr = item->init_expr;
  if (!expr || expr->kind != ExprKind::kSystemCall) return;

  auto name = expr->callee;
  bool is_fatal = name == "$fatal";
  bool is_error = name == "$error";
  bool is_warning = name == "$warning";
  bool is_info = name == "$info";
  if (!is_fatal && !is_error && !is_warning && !is_info) return;

  size_t arg_start = 0;
  if (is_fatal && !expr->args.empty()) {
    auto* first_arg = expr->args[0];
    if (first_arg->kind == ExprKind::kIntegerLiteral) {
      auto val = first_arg->int_val;
      if (val < 0 || val > 2) {
        diag_.Error(first_arg->range.start,
                    "finish_number must be 0, 1, or 2");
      }
      arg_start = 1;
    }
  }

  // Per §20.10.1, list_of_arguments may only contain a formatting string and
  // constant expressions, including constant function calls.
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  for (size_t i = arg_start; i < expr->args.size(); ++i) {
    auto* arg = expr->args[i];
    if (!arg) continue;
    if (i == arg_start && arg->kind == ExprKind::kStringLiteral) continue;
    if (arg->kind == ExprKind::kStringLiteral) continue;
    if (!IsConstantExpr(arg, scope)) {
      diag_.Error(arg->range.start,
                  std::format("argument to {} must be a constant expression "
                              "(§20.10.1)",
                              name));
    }
  }

  std::string scope_name = mod ? std::string(mod->name) : std::string{};
  if (!gen_prefix_.empty()) {
    std::string trimmed = gen_prefix_;
    while (!trimmed.empty() && trimmed.back() == '_') trimmed.pop_back();
    if (!trimmed.empty()) {
      if (!scope_name.empty()) scope_name.push_back('.');
      scope_name += trimmed;
    }
  }

  std::string severity;
  if (is_fatal) severity = "FATAL";
  else if (is_error) severity = "ERROR";
  else if (is_warning) severity = "WARNING";
  else severity = "INFO";

  std::string user_msg;
  if (arg_start < expr->args.size() &&
      expr->args[arg_start]->kind == ExprKind::kStringLiteral) {
    user_msg = std::string(expr->args[arg_start]->text);
    if (user_msg.size() >= 2 && user_msg.front() == '"' &&
        user_msg.back() == '"') {
      user_msg = user_msg.substr(1, user_msg.size() - 2);
    }
  }

  std::string message =
      scope_name.empty()
          ? std::format("elaboration {}: {}", severity, user_msg)
          : std::format("elaboration {} in scope '{}': {}", severity,
                        scope_name, user_msg);

  // Per §20.10.1, $fatal and $error block simulation; $warning and $info do
  // not affect the rest of elaboration or simulation. All four shall emit a
  // tool-specific message that names the call site (file/line carried by
  // the DiagEngine, scope embedded in the message body).
  diag_.Warning(item->loc, message);
  elab_last_severity_ = severity;
  elab_last_severity_msg_ = user_msg;
  elab_last_severity_scope_ = scope_name;
  elab_last_severity_loc_ = item->loc;
  if (is_fatal || is_error) {
    elab_simulation_blocked_ = true;
  }
}

// §11.12: map an explicitly-typed let formal's data type onto the categories
// the type rule cares about. An implicit type (a bare name, signing, or range,
// and also the `untyped` keyword, which leaves the type implicit) is not a
// "typed" formal, so it is reported separately by the caller. `event` is its
// own category; the integral, real, string, and user-defined types stand in
// for the §16.6-allowed type list; chandle, void, virtual interface, and the
// net kinds are outside that list.
static LetFormalTypeKind ClassifyLetFormalType(const DataType& dt) {
  switch (dt.kind) {
    case DataTypeKind::kImplicit:
      return LetFormalTypeKind::kUntyped;
    case DataTypeKind::kEvent:
      return LetFormalTypeKind::kEvent;
    case DataTypeKind::kVoid:
    case DataTypeKind::kChandle:
    case DataTypeKind::kVirtualInterface:
    case DataTypeKind::kWire:
    case DataTypeKind::kTri:
    case DataTypeKind::kWand:
    case DataTypeKind::kWor:
    case DataTypeKind::kTriand:
    case DataTypeKind::kTrior:
    case DataTypeKind::kTri0:
    case DataTypeKind::kTri1:
    case DataTypeKind::kTrireg:
    case DataTypeKind::kSupply0:
    case DataTypeKind::kSupply1:
    case DataTypeKind::kUwire:
      return LetFormalTypeKind::kForbidden;
    default:
      // Integral, real, string, named, enum, struct, and union types are all
      // usable in the §16.6 contexts a let body forms.
      return LetFormalTypeKind::kTypeAllowedIn16_6;
  }
}

void Elaborator::ValidateLetDecl(const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    LetFormalTypeKind kind = ClassifyLetFormalType(arg.data_type);
    if (!IsLetFormalTypeAllowed(kind)) {
      diag_.Error(item->loc,
                  std::format("let formal argument '{}' must be of type event "
                              "or a type allowed in a Boolean expression "
                              "(§11.12)",
                              arg.name));
    }
  }
}

void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  if (item->data_type.packed_dim_left && item->data_type.packed_dim_right) {
    var.width = EvalTypeWidth(item->data_type);
    if (var.width == 0) var.width = 32;
  } else {
    var.width = 32;
  }
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
}

static bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return true;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return true;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return true;
  }
  return false;
}

static uint32_t FindSignalWidth(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

static NetType FindSignalNetType(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.net_type;
  }
  return NetType::kNone;
}

static DataTypeKind NormalizeForCompatibility(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
    case DataTypeKind::kTri:
    case DataTypeKind::kWand:
    case DataTypeKind::kTriand:
    case DataTypeKind::kWor:
    case DataTypeKind::kTrior:
    case DataTypeKind::kTri0:
    case DataTypeKind::kTri1:
    case DataTypeKind::kTrireg:
    case DataTypeKind::kSupply0:
    case DataTypeKind::kSupply1:
    case DataTypeKind::kUwire:
      return DataTypeKind::kLogic;
    default:
      return kind;
  }
}

static int NetTypeGroup(NetType t) {
  switch (t) {
    case NetType::kWire:
    case NetType::kTri:
      return 0;
    case NetType::kWand:
    case NetType::kTriand:
      return 1;
    case NetType::kWor:
    case NetType::kTrior:
      return 2;
    case NetType::kTrireg:
      return 3;
    case NetType::kTri0:
      return 4;
    case NetType::kTri1:
      return 5;
    case NetType::kUwire:
      return 6;
    case NetType::kSupply0:
      return 7;
    case NetType::kSupply1:
      return 8;
    default:
      return -1;
  }
}

static bool DissimilarNetTypeRequiresWarning(NetType internal,
                                             NetType external) {
  static constexpr bool kWarnTable[9][9] = {

      {false, false, false, false, false, false, false, false, false},
      {false, false, true, true, true, true, true, false, false},
      {false, true, false, true, true, true, true, false, false},
      {false, true, true, false, false, false, true, false, false},
      {false, true, true, false, false, true, true, false, false},
      {false, true, true, false, true, false, true, false, false},
      {false, true, true, true, true, true, false, false, false},
      {false, false, false, false, false, false, false, false, true},
      {false, false, false, false, false, false, false, true, false},
  };
  int ig = NetTypeGroup(internal);
  int eg = NetTypeGroup(external);
  if (ig < 0 || eg < 0) return false;
  return kWarnTable[ig][eg];
}

static NetType PortNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
      return NetType::kWire;
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kNone;
  }
}

namespace {

struct ScopeWalk {
  std::vector<std::pair<std::string_view, SourceLoc>> block_labels;
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
};

void CollectScopeWalk(const Stmt* s, ScopeWalk& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock && !s->label.empty()) {
    out.block_labels.emplace_back(s->label, s->range.start);
  }
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.local_names.insert(s->var_name);
  }
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
    out.proc_lhs.emplace_back(s->lhs->text, s->range.start);
  }
  for (const auto* sub : s->stmts) CollectScopeWalk(sub, out);
  for (const auto* sub : s->fork_stmts) CollectScopeWalk(sub, out);
  CollectScopeWalk(s->then_branch, out);
  CollectScopeWalk(s->else_branch, out);
  CollectScopeWalk(s->body, out);
  CollectScopeWalk(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectScopeWalk(fi, out);
  for (const auto* fs : s->for_steps) CollectScopeWalk(fs, out);
  for (const auto& ci : s->case_items) CollectScopeWalk(ci.body, out);
}

bool IsProcBodyItem(ModuleItemKind k) {
  return k == ModuleItemKind::kInitialBlock ||
         k == ModuleItemKind::kFinalBlock ||
         k == ModuleItemKind::kAlwaysBlock ||
         k == ModuleItemKind::kAlwaysCombBlock ||
         k == ModuleItemKind::kAlwaysFFBlock ||
         k == ModuleItemKind::kAlwaysLatchBlock;
}

}  // namespace

namespace {

void WalkExprIdents(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    WalkExprIdents(e->lhs, out);
    return;
  }
  WalkExprIdents(e->lhs, out);
  WalkExprIdents(e->rhs, out);
  WalkExprIdents(e->base, out);
  WalkExprIdents(e->index, out);
  WalkExprIdents(e->index_end, out);
  WalkExprIdents(e->condition, out);
  WalkExprIdents(e->true_expr, out);
  WalkExprIdents(e->false_expr, out);
  WalkExprIdents(e->repeat_count, out);
  WalkExprIdents(e->with_expr, out);
  for (const auto* a : e->args) WalkExprIdents(a, out);
  for (const auto* el : e->elements) WalkExprIdents(el, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  WalkExprIdents(s->condition, out);
  WalkExprIdents(s->lhs, out);
  WalkExprIdents(s->rhs, out);
  WalkExprIdents(s->delay, out);
  WalkExprIdents(s->cycle_delay, out);
  WalkExprIdents(s->for_cond, out);
  WalkExprIdents(s->expr, out);
  WalkExprIdents(s->assert_expr, out);
  WalkExprIdents(s->repeat_event_count, out);
  WalkExprIdents(s->var_init, out);
  for (const auto* e : s->wait_order_events) WalkExprIdents(e, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) WalkExprIdents(p, out);
    WalkStmtIdents(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    WalkExprIdents(w, out);
    WalkStmtIdents(body, out);
  }
  for (const auto* sub : s->stmts) WalkStmtIdents(sub, out);
  for (const auto* sub : s->fork_stmts) WalkStmtIdents(sub, out);
  WalkStmtIdents(s->then_branch, out);
  WalkStmtIdents(s->else_branch, out);
  WalkStmtIdents(s->body, out);
  WalkStmtIdents(s->for_body, out);
  for (const auto* fi : s->for_inits) WalkStmtIdents(fi, out);
  for (const auto* fs : s->for_steps) WalkStmtIdents(fs, out);
  WalkStmtIdents(s->assert_pass_stmt, out);
  WalkStmtIdents(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidatePackageImportRules(const ModuleDecl* decl) {
  explicit_imports_.clear();
  wildcard_packages_.clear();
  wildcard_claimed_.clear();

  wildcard_packages_.push_back("std");

  auto package_declared = [&](std::string_view pkg_name) {
    if (pkg_name == "std") return true;
    for (const auto* pkg : unit_->packages) {
      if (pkg->name == pkg_name) return true;
    }
    return false;
  };

  auto provides = [&](std::string_view pkg_name,
                      std::string_view name) -> bool {
    auto it = pkg_provided_names_.find(pkg_name);
    if (it == pkg_provided_names_.end()) {
      auto& s = pkg_provided_names_[pkg_name];
      for (const auto* pkg : unit_->packages) {
        if (pkg->name != pkg_name) continue;
        for (const auto* pi : pkg->items) {
          if (!pi->name.empty()) s.insert(pi->name);
          if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
              !pi->class_decl->name.empty()) {
            s.insert(pi->class_decl->name);
          }
        }
      }
      it = pkg_provided_names_.find(pkg_name);
    }
    return it->second.count(name) != 0;
  };

  std::unordered_set<std::string_view> seen_decls;
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) seen_decls.insert(port.name);
  }
  for (const auto& [pname, pval] : decl->params) {
    if (!pname.empty()) seen_decls.insert(pname);
  }

  auto track_decl = [&](std::string_view name, SourceLoc loc) {
    if (name.empty()) return;
    auto wit = wildcard_claimed_.find(name);
    if (wit != wildcard_claimed_.end()) {
      diag_.Error(loc, std::format("declaration of '{}' follows a reference "
                                   "resolved through a wildcard package import",
                                   name));
    }
    seen_decls.insert(name);
  };

  auto process_ref = [&](const Expr* e) {
    auto name = e->text;
    if (name.empty()) return;
    if (seen_decls.count(name)) return;
    std::vector<std::string_view> providers;
    for (auto pkg : wildcard_packages_) {
      if (provides(pkg, name)) providers.push_back(pkg);
    }
    if (providers.size() > 1) {
      diag_.Error(e->range.start,
                  std::format("reference to '{}' is ambiguous between wildcard "
                              "imports of packages '{}' and '{}'",
                              name, providers[0], providers[1]));
      return;
    }
    if (providers.size() == 1) {
      wildcard_claimed_[name] = e->range.start;
      seen_decls.insert(name);
    }
  };

  for (const auto* item : decl->items) {
    switch (item->kind) {
      case ModuleItemKind::kImportDecl: {
        auto pkg_name = item->import_item.package_name;
        if (!package_declared(pkg_name)) {
          diag_.Error(
              item->loc,
              std::format("import from unknown package '{}'; the package "
                          "must be declared before any scope that imports "
                          "from it",
                          pkg_name));
          break;
        }
        if (item->import_item.is_wildcard) {
          if (std::find(wildcard_packages_.begin(), wildcard_packages_.end(),
                        pkg_name) == wildcard_packages_.end()) {
            wildcard_packages_.push_back(pkg_name);
          }
          break;
        }
        auto name = item->import_item.item_name;
        auto eit = explicit_imports_.find(name);
        if (eit != explicit_imports_.end()) {
          if (eit->second.first == pkg_name) break;
          diag_.Error(
              item->loc,
              std::format("explicit import of '{}::{}' conflicts with earlier "
                          "explicit import from '{}'",
                          pkg_name, name, eit->second.first));
          break;
        }
        if (seen_decls.count(name)) {
          auto wit = wildcard_claimed_.find(name);
          if (wit != wildcard_claimed_.end()) {
            diag_.Error(
                item->loc,
                std::format("explicit import of '{}::{}' is illegal because "
                            "'{}' was already referenced through a wildcard "
                            "package import",
                            pkg_name, name, name));
          } else {
            diag_.Error(item->loc,
                        std::format("explicit import of '{}::{}' collides with "
                                    "existing declaration of '{}'",
                                    pkg_name, name, name));
          }
          break;
        }
        explicit_imports_[name] = {pkg_name, item->loc};
        seen_decls.insert(name);
        break;
      }
      case ModuleItemKind::kInitialBlock:
      case ModuleItemKind::kFinalBlock:
      case ModuleItemKind::kAlwaysBlock:
      case ModuleItemKind::kAlwaysCombBlock:
      case ModuleItemKind::kAlwaysFFBlock:
      case ModuleItemKind::kAlwaysLatchBlock: {
        std::vector<const Expr*> refs;
        WalkStmtIdents(item->body, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kContAssign: {
        std::vector<const Expr*> refs;
        WalkExprIdents(item->assign_lhs, refs);
        WalkExprIdents(item->assign_rhs, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kModuleInst:
        track_decl(item->inst_name, item->loc);
        break;
      case ModuleItemKind::kGateInst:
      case ModuleItemKind::kUdpInst:
        track_decl(item->gate_inst_name, item->loc);
        break;
      case ModuleItemKind::kClassDecl:
        if (item->class_decl) track_decl(item->class_decl->name, item->loc);
        break;
      default:
        track_decl(item->name, item->loc);
        break;
    }
  }
}

void Elaborator::ValidateScopeRules(const ModuleDecl* decl) {
  ScopeWalk walk;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CollectScopeWalk(item->body, walk);
    }
  }
  for (const auto& [label, loc] : walk.block_labels) {
    if (!declared_names_.insert(label).second) {
      diag_.Error(loc, std::format("redeclaration of '{}'", label));
    }
  }
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (walk.local_names.count(name)) continue;
    if (declared_names_.count(name)) continue;
    if (ansi_port_names_.count(name)) continue;
    if (non_ansi_complete_ports_.count(name)) continue;
    if (non_ansi_partial_ports_.count(name)) continue;
    if (const_names_.count(name)) continue;
    if (enum_member_names_.count(name)) continue;
    if (specparam_names_.count(name)) continue;
    if (class_names_.count(name)) continue;
    if (class_var_names_.count(name)) continue;
    if (task_names_.count(name)) continue;
    if (func_decls_.count(name)) continue;
    if (interface_inst_types_.count(name)) continue;
    if (checker_inst_names_.count(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name));
  }
}

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  if (IsNameDeclared(name, mod)) return true;
  if (unit_->default_nettype == NetType::kNone) {
    diag_.Error(loc, std::format("implicit net '{}' forbidden by "
                                 "`default_nettype none",
                                 name));
    return false;
  }
  // §6.10: an identifier used in an instance terminal/port-connection list or
  // on the left side of a continuous assignment gets an implicit scalar net of
  // the default net type. It shares the implicit-net constructor with the
  // port-expression case; here the width is scalar and the net is unsigned.
  RtlirNet net = MakeImplicitPortNet(ScopedName(name), /*port_width=*/1,
                                     /*port_is_signed=*/false,
                                     unit_->default_nettype);
  mod->nets.push_back(net);
  declared_names_.insert(name);
  net_names_.insert(name);
  return true;
}

void Elaborator::ValidateContAssignIdentLhs(ModuleItem* item,
                                            RtlirModule* mod) {
  auto name = item->assign_lhs->text;
  MaybeCreateImplicitNet(name, item->loc, mod);
  if (!cont_assign_targets_.emplace(name, item->loc).second) {
    if (net_names_.count(name) == 0) {
      diag_.Error(item->loc,
                  std::format("multiple continuous assignments to '{}'", name));
    } else {
      auto it = var_types_.find(name);
      if (it != var_types_.end() && it->second == DataTypeKind::kUwire) {
        diag_.Error(
            item->loc,
            std::format("uwire '{}' cannot have multiple drivers", name));
      }
    }
  }
  if (var_init_names_.count(name) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both an initializer and a "
                            "continuous assignment",
                            name));
  }
}

void Elaborator::ValidateContAssignNettypeAndDelay(ModuleItem* item) {
  if (item->assign_lhs->kind == ExprKind::kSelect) {
    auto* base = item->assign_lhs->base;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select");
    }
  }
  if (item->assign_lhs->kind == ExprKind::kMemberAccess) {
    auto* base = item->assign_lhs->lhs;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select");
    }
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0) {
    if (item->assign_delay_fall || item->assign_delay_decay) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall have at most "
                  "a single delay");
    }
  }
}

void Elaborator::ValidateContAssignDriveStrength(ModuleItem* item,
                                                 RtlirModule* mod) {
  if (item->assign_lhs->kind != ExprKind::kIdentifier) return;
  uint32_t lhs_width = LookupLhsWidth(item->assign_lhs, mod);
  if (lhs_width <= 1) return;
  bool is_supply = false;
  for (const auto& n : mod->nets) {
    if (n.name == item->assign_lhs->text) {
      is_supply =
          (n.net_type == NetType::kSupply0 || n.net_type == NetType::kSupply1);
      break;
    }
  }
  if (!is_supply) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }
}

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier) {
    ValidateContAssignIdentLhs(item, mod);

    bool is_var_target = net_names_.count(item->assign_lhs->text) == 0;
    if (is_var_target) {
      if (item->drive_strength0 != 0 || item->drive_strength1 != 0) {
        diag_.Error(item->loc,
                    "drive strength not allowed on continuous assignment "
                    "to a variable");
      }
      if (item->assign_delay_fall || item->assign_delay_decay) {
        diag_.Error(item->loc,
                    "multiple delays not allowed on continuous assignment "
                    "to a variable");
      }
    }
  }
  if (item->assign_lhs) {
    ValidateContAssignNettypeAndDelay(item);
  }
  if ((item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      item->assign_lhs) {
    ValidateContAssignDriveStrength(item, mod);
  }
  RtlirContAssign ca;
  ca.lhs = item->assign_lhs;
  ca.rhs = item->assign_rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;

  ca.attrs = ResolveAttributes(item->attrs, diag_);
  mod->assigns.push_back(ca);
}

void Elaborator::ValidateTypenameAsElabConstant(const Expr* init) {
  if (init->kind != ExprKind::kSystemCall) return;
  if (init->callee != "$typename") return;
  if (init->args.empty()) return;
  const auto* arg = init->args[0];
  if (arg->kind == ExprKind::kMemberAccess) {
    diag_.Error(arg->range.start,
                "$typename argument in elaboration-time-constant context "
                "shall not contain hierarchical references");
    return;
  }
  if (arg->kind != ExprKind::kSelect) return;
  auto it = var_array_info_.find(arg->base->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_dynamic && !it->second.is_assoc) return;
  diag_.Error(arg->range.start,
              "$typename argument in elaboration-time-constant context "
              "shall not reference elements of dynamic objects");
}

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;

  // §6.20.3: a data type parameter (parameter type) can only be set to a data
  // type. The parser marks a type parameter with a void data type; if such a
  // parameter received an ordinary value expression instead of a type, it has
  // been set to a non-type and must be rejected.
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->init_expr != nullptr) {
    diag_.Error(item->loc,
                std::format("type parameter '{}' can only be set to a data "
                            "type, not a value expression",
                            item->name));
  }

  // §6.20.3: a type parameter declared with a leading enum, struct, or union
  // keyword restricts its valid types; assigning a type that does not conform
  // to that basic data type is an error. Resolve the assigned type through any
  // typedef chain and flag only a definite kind mismatch, leaving an
  // unresolved named type alone.
  if (is_type && (item->forward_type_kind == DataTypeKind::kEnum ||
                  item->forward_type_kind == DataTypeKind::kStruct ||
                  item->forward_type_kind == DataTypeKind::kUnion)) {
    const DataType* resolved = &item->typedef_type;
    for (int hops = 0; hops < 8 && resolved->kind == DataTypeKind::kNamed;
         ++hops) {
      auto td = typedefs_.find(resolved->type_name);
      if (td == typedefs_.end()) break;
      resolved = &td->second;
    }
    if (resolved->kind != DataTypeKind::kNamed &&
        resolved->kind != item->forward_type_kind) {
      static const auto basic_name = [](DataTypeKind k) -> std::string_view {
        switch (k) {
          case DataTypeKind::kEnum:
            return "enum";
          case DataTypeKind::kStruct:
            return "struct";
          case DataTypeKind::kUnion:
            return "union";
          default:
            return "type";
        }
      };
      diag_.Error(
          item->loc,
          std::format("type parameter '{}' is assigned a type that does "
                      "not conform to the required {} kind",
                      item->name, basic_name(item->forward_type_kind)));
    }
  }

  if (is_type) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.is_type_param = is_type;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!is_type) {
    PopulateParamTypeInfo(pd, item->data_type);
    // §11.5.1: a bit-select or part-select of a real parameter is illegal.
    // A real parameter holds a single scalar value, so record it alongside
    // scalar variables; any select applied to it is then rejected.
    DataTypeKind pk = item->data_type.kind;
    if (pk == DataTypeKind::kReal || pk == DataTypeKind::kShortreal ||
        pk == DataTypeKind::kRealtime) {
      scalar_var_names_.insert(item->name);
    }
  }

  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      item->init_expr->text == "$") {
    pd.is_unbounded = true;
  } else if (item->init_expr &&
             item->init_expr->kind == ExprKind::kIdentifier &&
             RefersToUnboundedParam(mod, item->init_expr->text)) {
    // §6.20.7: it is legal to assign a $ (unbounded) parameter to another
    // parameter; the assigned-to parameter is itself unbounded.
    pd.is_unbounded = true;
  } else if (item->init_expr) {
    if (ContainsDollarSubexpr(item->init_expr)) {
      // §6.20.7: $ must be the entire, self-contained parameter value; it may
      // not be combined with operators or selects in this context.
      diag_.Error(item->loc,
                  std::format("'$' may only be assigned to parameter '{}' as a "
                              "complete, self-contained expression",
                              item->name));
    }
    ValidateTypenameAsElabConstant(item->init_expr);
    auto scope = BuildParamScope(mod);
    auto val = ConstEvalInt(item->init_expr, scope);
    if (val) {
      pd.resolved_value = *val;
      pd.is_resolved = true;
    } else if (!is_type && ParamExpectsIntegerValue(pd, item->data_type)) {
      // §6.20.2: the real-to-integer conversion of §6.12.1 applies to
      // parameters, so an integer-typed parameter initialized from a real
      // constant rounds to the nearest integer (ties away from zero).
      if (auto rval = ConstEvalReal(item->init_expr, scope)) {
        pd.resolved_value = std::llround(*rval);
        pd.is_resolved = true;
      }
    }
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      break;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      break;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      break;
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_, diag_,
                 &func_decls_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      pending_generates_.push_back({item, mod});
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:

      if (!item->name.empty() && !declared_names_.insert(item->name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->name));
      }

      if (item->method_class.empty() &&
          (item->is_method_initial || item->is_method_extends ||
           item->is_method_final)) {
        diag_.Error(item->loc,
                    "dynamic_override_specifiers shall only be legal on "
                    "method declarations inside a non-interface class scope");
      }
      ValidateFunctionBody(item);
      ValidateFunctionArgDefaultsScope(item);
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:

      if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
          item->gate_terminals[0] &&
          item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
          item->gate_terminals[0]->text == item->gate_inst_name) {
        diag_.Error(item->loc,
                    std::format("gate instance name '{}' conflicts with its "
                                "output net",
                                item->gate_inst_name));
      }

      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->gate_inst_name));
      }

      // §6.10: an undeclared identifier used in a primitive instance's
      // terminal list is assumed to be an implicit scalar net of the default
      // net type, the same assumption made for a module instance's port
      // connections.
      for (auto* term : item->gate_terminals) {
        if (term && term->kind == ExprKind::kIdentifier)
          MaybeCreateImplicitNet(term->text, item->loc, mod);
      }

      if (item->inst_range_left && item->inst_range_right) {
        auto range_scope = BuildParamScope(mod);
        auto lhi = ConstEvalInt(item->inst_range_left, range_scope);
        auto rhi = ConstEvalInt(item->inst_range_right, range_scope);
        if (!lhi || !rhi) {
          diag_.Error(item->loc,
                      "gate or switch instance range bound is not a constant "
                      "expression");
        } else {
          uint32_t array_len = static_cast<uint32_t>(std::abs(*lhi - *rhi) + 1);
          for (auto* term : item->gate_terminals) {
            uint32_t w = LookupLhsWidth(term, mod);
            if (w == 0) continue;
            // §28.3.6: an interconnect port or interconnect net expression
            // connected to an instance array shall have a bit-length equal to
            // the instance-array length. Unlike an ordinary scalar terminal it
            // cannot be broadcast (width 1) across the instances.
            bool is_interconnect = term &&
                                   term->kind == ExprKind::kIdentifier &&
                                   interconnect_names_.count(term->text) != 0;
            if (is_interconnect) {
              if (w != array_len) {
                diag_.Error(item->loc,
                            "interconnect terminal of a gate instance array "
                            "must have a bit-length equal to the instance-array "
                            "length");
                break;
              }
              continue;
            }
            if (w != 1 && w != array_len) {
              diag_.Error(item->loc,
                          "gate array terminal width does not match either "
                          "the per-instance port width or the instance-array "
                          "length");
              break;
            }
          }
        }
      }
      ValidateBidirectionalSwitchConnections(item, mod, diag_,
                                             nettype_canonical_);
      ValidatePrimitiveOutputTerminalWidths(item, mod, diag_);
      ElaborateGateInst(item, mod, arena_);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kUdpInst:

      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->gate_inst_name));
      }
      // §6.10: undeclared identifiers in a UDP instance's terminal list also
      // become implicit scalar nets of the default net type.
      for (auto* term : item->gate_terminals) {
        if (term && term->kind == ExprKind::kIdentifier)
          MaybeCreateImplicitNet(term->text, item->loc, mod);
      }
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      break;
    case ModuleItemKind::kAlias: {
      for (auto* net : item->alias_nets) {
        if (net && net->kind == ExprKind::kIdentifier) {
          MaybeCreateImplicitNet(net->text, item->loc, mod);
        }
      }
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      break;
    }
    case ModuleItemKind::kSequenceDecl:
      sequence_names_.insert(item->name);
      mod->sequence_decls.push_back(item);
      // §16.8: a cyclic dependency among named sequences is an error.
      // PropertyRegistry has all sequence decls registered before any item
      // is elaborated (see ElaborateModule), so this DFS sees the full
      // graph regardless of declaration order.
      if (property_registry_.HasCyclicSequenceDependency(item)) {
        diag_.Error(item->loc,
                    "cyclic dependency among named sequences involving \"" +
                        std::string(item->name) + "\" (§16.8)");
      }
      // §16.10: a name that is already a formal argument of the sequence
      // declaration may not be redeclared as a body-scope local variable.
      ValidateNoFormalShadowedByBodyLocal(item);
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kDefparam:
      break;
    case ModuleItemKind::kImportDecl: {
      RtlirImport imp;
      imp.package_name = item->import_item.package_name;
      imp.item_name = item->import_item.item_name;
      imp.is_wildcard = item->import_item.is_wildcard;
      mod->imports.push_back(imp);
      break;
    }
    case ModuleItemKind::kExportDecl:

      break;
    case ModuleItemKind::kPropertyDecl: {
      // §16.12: nesting of disable iff is forbidden, explicitly or through
      // property instantiations. The flattened count via §F.4.1's rewriter
      // catches both cases.
      int flat_disable_iff = property_registry_.FlattenedDisableIffCount(item);
      if (flat_disable_iff > 1) {
        diag_.Error(item->loc, "property \"" + std::string(item->name) +
                                   "\" nests disable iff clauses (§16.12)");
      }
      // §16.10: same formal-vs-body shadow rule applies to a property
      // declaration: a formal-argument name cannot be redeclared as a
      // body-scope local variable.
      ValidateNoFormalShadowedByBodyLocal(item);
      // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
      ValidateRecursiveProperty(item);
      ValidateClockingBlock(item, mod);
      break;
    }
    case ModuleItemKind::kAssertProperty:
      // §16.4.3: a deferred immediate assertion (assert/assume/cover with #0
      // or final) written directly as a module item, outside any procedure, is
      // a static deferred assertion. It is treated as if it were the sole
      // statement of an always_comb procedure, so build that implicit process
      // here rather than routing it through the concurrent-assertion path. The
      // parser wraps every module-level deferred immediate form under the
      // kAssertProperty kind, distinguished by a deferred statement body.
      if (item->body && item->body->is_deferred) {
        AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, arena_, diag_,
                   &func_decls_);
        break;
      }
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item, mod);
      break;
    case ModuleItemKind::kDpiImport:
      ValidateDpiImport(item);
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kLetDecl:
      ValidateLetDecl(item);
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSpecifyBlock:
    case ModuleItemKind::kDpiExport:
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kDefaultDisableIff:
    case ModuleItemKind::kNestedModuleDecl:
      break;
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        class_names_.insert(item->class_decl->name);
        if (!item->class_decl->params.empty())
          parameterized_class_names_.insert(item->class_decl->name);
        mod->class_decls.push_back(item->class_decl);
      }
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  static const auto kind_name = [](DataTypeKind k) -> std::string_view {
    switch (k) {
      case DataTypeKind::kEnum:
        return "enum";
      case DataTypeKind::kStruct:
        return "struct";
      case DataTypeKind::kUnion:
        return "union";
      default:
        return "type";
    }
  };
  bool is_forward = item->typedef_type.kind == DataTypeKind::kImplicit;
  if (is_forward) {
    if (item->forward_type_kind != DataTypeKind::kImplicit) {
      auto td_it = typedefs_.find(item->name);
      if (td_it != typedefs_.end() &&
          td_it->second.kind != DataTypeKind::kImplicit &&
          td_it->second.kind != item->forward_type_kind) {
        diag_.Error(
            item->loc,
            std::format("forward typedef '{}' as {} does not conform "
                        "to its existing definition",
                        item->name, kind_name(item->forward_type_kind)));
      }
      forward_typedef_kinds_[item->name] = item->forward_type_kind;
    }

    typedefs_.try_emplace(item->name, item->typedef_type);
    return;
  }
  auto it = forward_typedef_kinds_.find(item->name);
  if (it != forward_typedef_kinds_.end() &&
      it->second != item->typedef_type.kind) {
    diag_.Error(item->loc,
                std::format("typedef '{}' does not conform to its forward "
                            "declaration as {}",
                            item->name, kind_name(it->second)));
  }
  typedefs_[item->name] = item->typedef_type;
  // §6.24.3: track typedefs whose first unpacked dimension is an associative
  // index, so the bit-stream cast validator can reject them as destinations.
  bool first_dim_assoc = false;
  if (!item->unpacked_dims.empty() && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    auto t = item->unpacked_dims[0]->text;
    if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
        t == "shortint" || t == "longint" || t == "*") {
      assoc_typedef_names_.insert(item->name);
      first_dim_assoc = true;
    } else if (typedefs_.count(t) > 0 || class_names_.count(t) > 0) {
      assoc_typedef_names_.insert(item->name);
      first_dim_assoc = true;
    }
  }
  // §6.24.3: when every unpacked dimension is a fixed integer size (no
  // dynamic, queue, or associative dim), the typedef has a known total bit
  // width that the bit-stream cast validator can compare against a source.
  if (!item->unpacked_dims.empty() && !first_dim_assoc) {
    uint32_t elem_width = EvalTypeWidth(item->typedef_type, typedefs_);
    uint64_t total = elem_width;
    bool all_fixed = (elem_width > 0);
    for (auto* dim : item->unpacked_dims) {
      if (!dim) {
        all_fixed = false;
        break;
      }
      if (dim->kind == ExprKind::kIdentifier) {
        auto t = dim->text;
        if (t == "$" || t == "*" || t == "string" || t == "int" ||
            t == "integer" || t == "byte" || t == "shortint" ||
            t == "longint") {
          all_fixed = false;
          break;
        }
      }
      if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
        auto lv = ConstEvalInt(dim->lhs);
        auto rv = ConstEvalInt(dim->rhs);
        if (!lv || !rv) {
          all_fixed = false;
          break;
        }
        int64_t span = std::abs(*lv - *rv) + 1;
        total *= static_cast<uint64_t>(span);
      } else {
        auto sv = ConstEvalInt(dim);
        if (!sv || *sv <= 0) {
          all_fixed = false;
          break;
        }
        total *= static_cast<uint64_t>(*sv);
      }
    }
    if (all_fixed && total > 0 && total < uint64_t{1} << 32) {
      fixed_unpacked_typedef_widths_[item->name] = static_cast<uint32_t>(total);
    }
  }
  if (item->typedef_type.kind == DataTypeKind::kStruct ||
      item->typedef_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->typedef_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->typedef_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->typedef_type, item->loc);
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  auto width = EvalTypeWidth(item->typedef_type, typedefs_);
  std::vector<RtlirEnumMember> members;
  for (const auto& member : item->typedef_type.enum_members) {
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }

    if (member.range_start) {
      auto n = ConstEvalInt(member.range_start).value_or(0);
      if (member.range_end) {
        auto m = ConstEvalInt(member.range_end).value_or(0);
        int step = (m >= n) ? 1 : -1;
        for (auto i = n;; i += step) {
          auto s = std::format("{}{}", member.name, i);
          auto* p = arena_.AllocString(s.c_str(), s.size());
          std::string_view sv{p, s.size()};
          enum_member_names_.insert(sv);
          members.push_back({sv, next_val});
          RtlirVariable var;
          var.name = sv;
          var.width = width;
          var.is_4state = false;
          mod->variables.push_back(var);
          ++next_val;
          if (i == m) break;
        }
      } else {
        for (int64_t i = 0; i < n; ++i) {
          auto s = std::format("{}{}", member.name, i);
          auto* p = arena_.AllocString(s.c_str(), s.size());
          std::string_view sv{p, s.size()};
          enum_member_names_.insert(sv);
          members.push_back({sv, next_val});
          RtlirVariable var;
          var.name = sv;
          var.width = width;
          var.is_4state = false;
          mod->variables.push_back(var);
          ++next_val;
        }
      }
    } else {
      enum_member_names_.insert(member.name);
      members.push_back({member.name, next_val});
      RtlirVariable var;
      var.name = member.name;
      var.width = width;
      var.is_4state = false;
      mod->variables.push_back(var);
      ++next_val;
    }
  }
  mod->enum_types[item->name] = std::move(members);
}

void Elaborator::ValidateForwardTypedefsInScope(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = false;
    for (const auto* other : decl->items) {
      if (other == item) continue;
      if (other->kind == ModuleItemKind::kTypedef &&
          other->name == item->name &&
          other->typedef_type.kind != DataTypeKind::kImplicit) {
        resolved = true;
        break;
      }
      if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
          other->class_decl->name == item->name) {
        resolved = true;
        break;
      }
    }
    if (!resolved && class_names_.count(item->name) > 0) {
      resolved = true;
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

void Elaborator::ValidateForwardTypedefScopePrefix(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kNamed) continue;
    if (item->typedef_type.scope_name.empty()) continue;
    auto scope = item->typedef_type.scope_name;
    bool is_forward_in_scope = false;
    bool resolves_to_class = class_names_.count(scope) > 0;
    for (const auto* other : decl->items) {
      if (other->kind == ModuleItemKind::kTypedef && other->name == scope &&
          other->typedef_type.kind == DataTypeKind::kImplicit) {
        is_forward_in_scope = true;
      }
      if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
          other->class_decl->name == scope) {
        resolves_to_class = true;
      }
    }
    if (!is_forward_in_scope) continue;
    if (!resolves_to_class) {
      diag_.Error(item->loc,
                  std::format("scope-resolution prefix '{}' of a typedef does "
                              "not resolve to a class",
                              scope));
    }
  }
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule*) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  if (!item->nettype_resolve_func.empty()) {
    nettype_resolve_funcs_[item->name] = item->nettype_resolve_func;
    nettype_canonical_[item->name] = item->name;
  } else if (item->typedef_type.kind == DataTypeKind::kNamed) {
    auto it = nettype_resolve_funcs_.find(item->typedef_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      nettype_resolve_funcs_[item->name] = it->second;
    }

    auto cit = nettype_canonical_.find(item->typedef_type.type_name);
    nettype_canonical_[item->name] = (cit != nettype_canonical_.end())
                                         ? cit->second
                                         : item->typedef_type.type_name;
  } else {
    nettype_canonical_[item->name] = item->name;
  }
}

// §6.22.6 Matching nettypes: a nettype matches itself (and the nettype of nets
// declared using it), and a simple nettype that renames a user-defined nettype
// matches the nettype it renames. Both cases reduce to comparing the canonical
// (source) nettype each name resolves to: an alias shares its source's
// canonical name, so it matches; unrelated nettypes have distinct canonical
// names, so they do not.
bool NettypesMatch(
    std::string_view a, std::string_view b,
    const std::unordered_map<std::string_view, std::string_view>&
        nettype_canonical) {
  if (a == b) return true;
  auto ait = nettype_canonical.find(a);
  auto bit = nettype_canonical.find(b);
  std::string_view ca = (ait != nettype_canonical.end()) ? ait->second : a;
  std::string_view cb = (bit != nettype_canonical.end()) ? bit->second : b;
  return ca == cb;
}

UdpDecl* Elaborator::FindUdpByName(std::string_view name) const {
  for (auto* u : unit_->udps) {
    if (u->name == name) return u;
  }
  return nullptr;
}

void Elaborator::ReclassifyForwardUdpInstances(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!FindUdpByName(item->inst_module)) continue;

    item->kind = ModuleItemKind::kUdpInst;
    item->gate_inst_name = item->inst_name;
    item->inst_name = {};
    item->gate_terminals.clear();
    item->gate_terminals.reserve(item->inst_ports.size());
    for (const auto& [pname, pexpr] : item->inst_ports) {
      item->gate_terminals.push_back(pexpr);
    }
    item->inst_ports.clear();
    item->inst_ports_implicit.clear();
  }
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  ReclassifyForwardUdpInstances(decl);

  forward_typedef_kinds_.clear();
  declared_names_.clear();
  net_names_.clear();
  cont_assign_targets_.clear();
  proc_assign_targets_.clear();
  var_types_.clear();
  var_array_info_.clear();
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
  const_names_.clear();
  class_var_names_.clear();
  class_var_types_.clear();
  var_init_names_.clear();
  output_port_targets_.clear();
  nettype_net_names_.clear();
  interconnect_names_.clear();
  scalar_var_names_.clear();
  var_named_types_.clear();
  alias_pairs_.clear();
  non_ansi_complete_ports_.clear();
  non_ansi_partial_ports_.clear();
  ansi_port_names_.clear();
  clocking_signals_.clear();
  interface_inst_types_.clear();
  vi_var_interface_types_.clear();
  vi_var_modports_.clear();
  vi_var_param_values_.clear();
  interface_inst_param_values_.clear();
  checker_inst_names_.clear();
  program_inst_names_.clear();
  auto_task_func_names_.clear();
  nested_module_decls_.clear();
  task_names_.clear();
  sequence_names_.clear();
  func_decls_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      nested_module_decls_[item->nested_module_decl->name] =
          item->nested_module_decl;
    }

    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(item->loc,
                  "virtual interface cannot be declared inside an interface");
    }
  }
  const bool parent_is_program = decl->decl_kind == ModuleDeclKind::kProgram;
  const bool parent_is_checker = decl->decl_kind == ModuleDeclKind::kChecker;
  const std::string_view parent_kind_word = parent_is_program
                                                ? std::string_view{"program"}
                                                : std::string_view{"checker"};

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      auto* child = FindModuleInScope(item->inst_module);
      if (child && child->decl_kind == ModuleDeclKind::kInterface) {
        interface_inst_types_[item->inst_name] = item->inst_module;
        // §25.9: record explicit parameter overrides (when they evaluate to
        // constants) so a later virtual-interface assignment can confirm the
        // actual parameter values match.
        if (!item->inst_params.empty()) {
          std::vector<int64_t> values;
          bool all_const = true;
          for (const auto& param : item->inst_params) {
            const Expr* pexpr = param.second;
            if (pexpr == nullptr) {
              all_const = false;
              break;
            }
            auto v = ConstEvalInt(pexpr);
            if (!v) {
              all_const = false;
              break;
            }
            values.push_back(*v);
          }
          if (all_const) {
            interface_inst_param_values_[item->inst_name] = std::move(values);
          }
        }
      }
      if (child && child->decl_kind == ModuleDeclKind::kChecker) {
        checker_inst_names_.insert(item->inst_name);
      }
      if (child && child->decl_kind == ModuleDeclKind::kProgram) {
        program_inst_names_.insert(item->inst_name);
      }
      if (decl->decl_kind == ModuleDeclKind::kInterface && child &&
          child->decl_kind == ModuleDeclKind::kModule) {
        diag_.Error(item->loc,
                    std::format("module '{}' cannot be instantiated inside "
                                "interface '{}'",
                                item->inst_module, decl->name));
      }
      if ((parent_is_program || parent_is_checker) && child &&
          child->decl_kind != ModuleDeclKind::kChecker) {
        diag_.Error(item->loc,
                    std::format("only checkers can be instantiated inside "
                                "{} '{}'",
                                parent_kind_word, decl->name));
      }
    }
    if ((parent_is_program || parent_is_checker) &&
        item->kind == ModuleItemKind::kUdpInst) {
      diag_.Error(item->loc,
                  std::format("primitive cannot be instantiated inside "
                              "{} '{}'",
                              parent_kind_word, decl->name));
    }

    // §17.7: a checker body may define variables (the checker variables of
    // §17.2's checker_or_generate_item_declaration), but defining nets in the
    // checker body is illegal.
    if (parent_is_checker && item->kind == ModuleItemKind::kNetDecl) {
      diag_.Error(item->loc,
                  std::format("a net cannot be declared inside checker '{}'; "
                              "only variables may be defined in a checker body",
                              decl->name));
    }

    // Annex C.2.7: the general-purpose always procedure in checkers is
    // deprecated and removed in this version of the standard. The specialized
    // always_comb, always_latch, and always_ff procedures have been added for
    // checkers and cover every case a general always could express, so a plain
    // always inside a checker body is rejected.
    if (parent_is_checker && item->kind == ModuleItemKind::kAlwaysBlock) {
      diag_.Error(item->loc,
                  std::format("a general 'always' procedure cannot be used "
                              "inside checker '{}'; use always_comb, "
                              "always_latch, or always_ff instead",
                              decl->name));
    }

    // §17.2: modules, interfaces, and programs shall not be declared inside a
    // checker. Only further checker declarations are permitted here.
    if (parent_is_checker && item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
      diag_.Error(item->loc,
                  std::format("a module, interface, or program cannot be "
                              "declared inside checker '{}'",
                              decl->name));
    }

    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram &&
        item->nested_module_decl->ports.empty()) {
      program_inst_names_.insert(item->nested_module_decl->name);
    }
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kModule) {
      diag_.Error(item->loc,
                  std::format("module '{}' cannot be declared inside "
                              "interface '{}'",
                              item->nested_module_decl->name, decl->name));
    }
  }

  for (const auto& [pname, pval] : decl->params) {
    const_names_.insert(pname);
  }

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names_.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls_[item->name] = item;
    }
  }

  for (auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        !item->is_automatic && !item->is_static) {
      if (decl->is_automatic) {
        item->is_automatic = true;
      } else {
        item->is_static = true;
      }
    }
  }

  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl) &&
        item->is_automatic) {
      auto_task_func_names_.insert(item->name);
    }
  }

  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());

  // §16.12 lets a property be instantiated before its declaration, and
  // §F.4.1 assumes names are resolved before the rewriter runs. Build the
  // property/sequence registry up-front so flatten works for any decl.
  property_registry_ = PropertyRegistry();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl ||
        item->kind == ModuleItemKind::kSequenceDecl) {
      property_registry_.Register(item);
    }
  }

  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }

  for (const auto& [name, nested_decl] : local_nested_modules) {
    if (!nested_decl->ports.empty()) continue;
    if (nested_decl->decl_kind == ModuleDeclKind::kInterface) continue;

    if (HasParamPortWithoutDefault(nested_decl)) continue;
    bool explicitly_instantiated = false;
    for (const auto& child : mod->children) {
      if (child.module_name == name) {
        explicitly_instantiated = true;
        break;
      }
    }
    if (explicitly_instantiated) continue;
    RtlirModuleInst inst;
    inst.module_name = name;
    inst.inst_name = name;
    ParamList empty_params;

    std::string saved_inst_path = current_inst_path_;
    if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
    current_inst_path_.append(name.data(), name.size());
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    mod->children.push_back(inst);
  }

  CheckAlwaysCombMultiDriver(decl, mod);
  ValidateModuleConstraints(decl);
  ValidateValueParams(decl, mod);
  ValidateLhsPatternWidths(decl, mod);
  ValidateClockvarAccess(decl);
  ValidateCycleDelayDefaultClocking(decl);
  ValidateIntraAssignCycleDelay(decl);
  ValidateDuplicateDefaultClocking(decl);
  ValidateDefaultClockingReference(decl);
  ValidateDuplicateGlobalClocking(decl);
  ValidateGlobalClockReference(decl);
  ValidateContAssignToClockvar(decl);
  ValidatePrimitiveDriveToClockvar(decl);
  ValidateSyncDriveForm(decl);
  ValidateConstantFunctionCalls(decl);
  ValidateDpiOpenArrayArgs(decl);
  ValidateBackgroundFuncCallContext(decl);
  ValidateSequenceEventArgs(decl);
  ValidateHierRefIntoChecker(decl);
  ValidateHierRefIntoProgram(decl);
  ValidateProgramSubroutineCall(decl);
  ValidateHierRefToAutomatic(decl);
  ValidateHierRefToImportedName(decl, mod);
  ValidateHierRefInstanceArray(decl);
  ValidateForwardTypedefsInScope(decl);
  ValidateForwardTypedefScopePrefix(decl);
}

namespace {

void CollectMemberAccess(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) {
    out.push_back(e);
  }
  CollectMemberAccess(e->lhs, out);
  CollectMemberAccess(e->rhs, out);
  CollectMemberAccess(e->base, out);
  CollectMemberAccess(e->index, out);
  CollectMemberAccess(e->index_end, out);
  CollectMemberAccess(e->condition, out);
  CollectMemberAccess(e->true_expr, out);
  CollectMemberAccess(e->false_expr, out);
  CollectMemberAccess(e->repeat_count, out);
  CollectMemberAccess(e->with_expr, out);
  for (const auto* a : e->args) CollectMemberAccess(a, out);
  for (const auto* el : e->elements) CollectMemberAccess(el, out);
}

void CollectMemberAccessInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  CollectMemberAccess(s->condition, out);
  CollectMemberAccess(s->lhs, out);
  CollectMemberAccess(s->rhs, out);
  CollectMemberAccess(s->delay, out);
  CollectMemberAccess(s->cycle_delay, out);
  CollectMemberAccess(s->for_cond, out);
  CollectMemberAccess(s->expr, out);
  CollectMemberAccess(s->assert_expr, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) CollectMemberAccess(p, out);
    CollectMemberAccessInStmt(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    CollectMemberAccess(w, out);
    CollectMemberAccessInStmt(body, out);
  }
  for (const auto* sub : s->stmts) CollectMemberAccessInStmt(sub, out);
  for (const auto* sub : s->fork_stmts) CollectMemberAccessInStmt(sub, out);
  CollectMemberAccessInStmt(s->then_branch, out);
  CollectMemberAccessInStmt(s->else_branch, out);
  CollectMemberAccessInStmt(s->body, out);
  CollectMemberAccessInStmt(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectMemberAccessInStmt(fi, out);
  for (const auto* fs : s->for_steps) CollectMemberAccessInStmt(fs, out);
  CollectMemberAccessInStmt(s->assert_pass_stmt, out);
  CollectMemberAccessInStmt(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidateHierRefToImportedName(const ModuleDecl* decl,
                                               const RtlirModule* mod) {
  if (!mod || mod->children.empty()) return;
  std::unordered_map<std::string_view, const RtlirModule*> inst_type;
  for (const auto& child : mod->children) {
    if (child.resolved) inst_type[child.inst_name] = child.resolved;
  }
  if (inst_type.empty()) return;

  auto imported_into = [&](const RtlirModule* m, std::string_view name) {
    for (const auto& imp : m->imports) {
      if (!imp.is_wildcard && imp.item_name == name) return true;
      if (imp.is_wildcard) {
        for (const auto* pkg : unit_->packages) {
          if (pkg->name != imp.package_name) continue;
          for (const auto* pi : pkg->items) {
            if (pi->name == name) return true;
            if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
                pi->class_decl->name == name)
              return true;
          }
        }
      }
    }
    return false;
  };

  auto check_member_access = [&](const Expr* ma) {
    if (!ma || ma->kind != ExprKind::kMemberAccess) return;
    if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
    if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
    auto it = inst_type.find(ma->lhs->text);
    if (it == inst_type.end()) return;
    if (imported_into(it->second, ma->rhs->text)) {
      diag_.Error(
          ma->range.start,
          std::format("hierarchical reference '{}.{}' targets a name imported "
                      "into '{}' from a package; imported names are not "
                      "visible through hierarchical references",
                      ma->lhs->text, ma->rhs->text, it->second->name));
    }
  };

  std::vector<const Expr*> accesses;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }
  for (const auto* ma : accesses) check_member_access(ma);
}

void Elaborator::ValidateHierRefInstanceArray(const ModuleDecl* decl) {
  struct ArrayBounds {
    int64_t low;
    int64_t high;
  };
  std::unordered_map<std::string_view, ArrayBounds> arrayed;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!item->inst_range_left || !item->inst_range_right) continue;
    auto lhi = ConstEvalInt(item->inst_range_left);
    auto rhi = ConstEvalInt(item->inst_range_right);
    if (!lhi || !rhi) continue;
    ArrayBounds b;
    b.low = std::min(*lhi, *rhi);
    b.high = std::max(*lhi, *rhi);
    arrayed[item->inst_name] = b;
  }
  if (arrayed.empty()) return;

  std::vector<const Expr*> accesses;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }

  for (const auto* ma : accesses) {
    if (!ma || ma->kind != ExprKind::kMemberAccess || !ma->lhs) continue;
    const Expr* base = ma->lhs;
    std::string_view name;
    const Expr* select_index = nullptr;
    if (base->kind == ExprKind::kIdentifier) {
      name = base->text;
    } else if (base->kind == ExprKind::kSelect && base->base &&
               base->base->kind == ExprKind::kIdentifier) {
      name = base->base->text;
      select_index = base->index;
    } else {
      continue;
    }
    auto it = arrayed.find(name);
    if (it == arrayed.end()) continue;
    if (!select_index) {
      diag_.Error(ma->range.start,
                  std::format("hierarchical reference to instance array '{}' "
                              "requires an instance select",
                              name));
      continue;
    }
    auto idx = ConstEvalInt(select_index);
    if (!idx) continue;
    if (*idx < it->second.low || *idx > it->second.high) {
      diag_.Error(select_index->range.start,
                  std::format("instance select [{}] is out of range for "
                              "instance array '{}' [{}:{}]",
                              *idx, name, it->second.high, it->second.low));
    }
  }
}

static uint32_t EvalInstDimSize(const Expr* left, const Expr* right) {
  if (left && right) {
    auto lv = ConstEvalInt(left);
    auto rv = ConstEvalInt(right);
    if (lv && rv) return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left);
    if (v && *v > 0) return static_cast<uint32_t>(*v);
  }
  return 0;
}

void Elaborator::ApplyConfigParamOverrides(
    const ModuleDecl* child_decl, ParamList& child_params,
    const ScopeMap& parent_scope, std::vector<std::string_view>& locked) {
  if (instance_param_overrides_.empty() || current_inst_path_.empty()) return;

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
  ScopeMap scope = parent_scope;
  for (const auto& [name, val] : config_localparam_scope_) {
    scope[name] = val;
  }

  auto drop = [&](std::string_view pname) {
    ParamList kept;
    kept.reserve(child_params.size());
    for (const auto& e : child_params) {
      if (e.first != pname) kept.push_back(e);
    }
    child_params.swap(kept);
  };

  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path != current_inst_path_) continue;

    if (ov.reset_all) {
      // "#()" returns every parameter to its module default: discard the
      // instantiation's overrides and let the configuration own each one.
      child_params.clear();
      for (const auto& [dname, dexpr] : child_decl->params) {
        (void)dexpr;
        if (child_decl->localparam_port_names.count(dname) > 0) continue;
        if (child_decl->type_param_names.count(dname) > 0) continue;
        locked.push_back(dname);
      }
    }

    for (const auto& [pname, pexpr] : ov.params) {
      // Replace any value the instantiation supplied; a present expression sets
      // a new value while a null one ("(.p())") leaves the parameter at its
      // module default. Either way the configuration now owns the parameter.
      drop(pname);
      if (pexpr) {
        if (auto val = ConstEvalInt(pexpr, scope)) {
          child_params.push_back({pname, *val});
        }
      }
      locked.push_back(pname);
    }
  }
}

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  if (!item->inst_name.empty() &&
      !declared_names_.insert(item->inst_name).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(item->inst_name.data(), item->inst_name.size());

  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) {
    if (item->inst_scope.empty())
      diag_.Error(item->loc,
                  std::format("unknown module '{}'", item->inst_module));
    else
      diag_.Error(item->loc, std::format("unknown module '{}::{}'",
                                         item->inst_scope, item->inst_module));
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    return;
  }

  auto saved_nested = nested_module_decls_;
  ParamList child_params;
  auto parent_scope = BuildParamScope(mod);

  bool is_positional = false;
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) {
      is_positional = true;
      break;
    }
  }

  if (is_positional) {
    std::vector<std::string_view> targets;
    for (const auto& [dname, dexpr] : child_decl->params) {
      if (child_decl->localparam_port_names.count(dname) > 0) continue;
      targets.push_back(dname);
    }
    if (item->inst_params.size() > targets.size()) {
      diag_.Error(
          item->loc,
          std::format("too many positional parameter overrides for module "
                      "'{}': {} provided, {} allowed",
                      item->inst_module, item->inst_params.size(),
                      targets.size()));
    }
    size_t n = std::min(item->inst_params.size(), targets.size());
    for (size_t i = 0; i < n; ++i) {
      auto* pexpr = item->inst_params[i].second;
      if (!pexpr) continue;
      auto val = ConstEvalInt(pexpr, parent_scope);
      if (val) child_params.push_back({targets[i], *val});
    }
  } else {
    std::unordered_set<std::string_view> overridable;
    for (const auto& [dname, dexpr] : child_decl->params) {
      if (child_decl->localparam_port_names.count(dname) > 0) continue;
      overridable.insert(dname);
    }
    for (const auto& [pname, pexpr] : item->inst_params) {
      if (overridable.count(pname) == 0) {
        diag_.Error(item->loc, std::format("module '{}' has no parameter '{}'",
                                           item->inst_module, pname));
        continue;
      }
      if (!pexpr) continue;
      auto val = ConstEvalInt(pexpr, parent_scope);
      if (val) child_params.push_back({pname, *val});
    }
  }

  // A configuration may override (or reset) this instance's parameters on top
  // of whatever the instantiation specified (§33.4.3).
  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(child_decl, child_params, parent_scope,
                            config_locked);

  inst.resolved = ElaborateModule(child_decl, child_params);
  nested_module_decls_ = std::move(saved_nested);

  // Mark parameters the configuration fixed so a later defparam cannot change
  // them: a config override takes precedence over defparam (§33.4.3).
  if (inst.resolved) {
    for (auto pname : config_locked) {
      for (auto& p : inst.resolved->params) {
        if (p.name == pname) {
          p.config_locked = true;
          break;
        }
      }
    }
  }
  BindPorts(inst, item, mod);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right);
    if (sz > 0) {
      inst_dim_sizes.push_back(sz);
      total_instances *= sz;
    }
  }

  if (!item->inst_dims.empty()) {
    ValidateInstanceArrayPorts(inst, item, mod, inst_dim_sizes,
                               total_instances);
  } else {
    ValidateUnpackedArrayPorts(inst, item, mod);
  }

  CheckPortCoercion(inst, item->loc);
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);

  inst.attrs = ResolveAttributes(item->attrs, diag_);
  mod->children.push_back(inst);
  current_inst_path_ = std::move(saved_inst_path);
}

Expr* Elaborator::MakePullExpr(NetType drive) {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIntegerLiteral;
  expr->int_val = (drive == NetType::kTri1) ? 1 : 0;
  return expr;
}

Expr* Elaborator::MakeHighZExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kUnbasedUnsizedLiteral;
  expr->text = "'z";
  return expr;
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const bool has_pull = unit_->unconnected_drive != NetType::kWire;

  const bool is_ordered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();

  // §23.3.3.2: connecting a child's port variable to an interconnect signal of
  // the instantiating module is illegal. The interconnect signal may be a local
  // interconnect net (recorded in interconnect_names_) or one of this module's
  // own interconnect ports threaded down through the hierarchy.
  auto connects_to_interconnect = [&](std::string_view conn_name) -> bool {
    if (interconnect_names_.count(conn_name)) return true;
    for (const auto& p : parent_mod->ports)
      if (p.name == conn_name && p.is_interconnect) return true;
    return false;
  };

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto& [port_name, conn_expr] = item->inst_ports[i];
    const bool is_implicit =
        i < item->inst_ports_implicit.size() && item->inst_ports_implicit[i];

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      if (is_implicit) {
        if (!IsNameDeclared(conn_expr->text, parent_mod)) {
          diag_.Error(
              item->loc,
              std::format(
                  "implicit named port connection '.{}' requires "
                  "signal '{}' to be declared in the instantiating scope",
                  port_name, conn_expr->text));
        }
      } else if (!interface_inst_types_.count(conn_expr->text)) {
        MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
      }
    }
    RtlirPortBinding binding;
    binding.connection = conn_expr;

    auto it = child_ports.end();
    if (is_ordered) {
      if (i < child_ports.size()) {
        it = child_ports.begin() + static_cast<ptrdiff_t>(i);
        binding.port_name = it->name;
      } else {
        diag_.Warning(
            item->loc,
            std::format("too many ordered port connections for module '{}'"
                        " (expected {}, got {})",
                        inst.module_name, child_ports.size(),
                        item->inst_ports.size()));
        break;
      }
    } else {
      binding.port_name = port_name;
      it =
          std::find_if(child_ports.begin(), child_ports.end(),
                       [&](const RtlirPort& p) { return p.name == port_name; });
    }

    if (it == child_ports.end()) {
      diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                           port_name, inst.module_name));
      binding.direction = Direction::kInput;
      binding.width = 1;
    } else {
      binding.direction = it->direction;
      binding.width = it->width;

      if (is_implicit && conn_expr &&
          IsNameDeclared(conn_expr->text, parent_mod)) {
        uint32_t sig_width = FindSignalWidth(conn_expr->text, parent_mod);
        if (sig_width != 0 && sig_width != it->width) {
          diag_.Error(
              item->loc,
              std::format("implicit named port connection '.{}' requires "
                          "equivalent data types (port width {}, "
                          "signal width {})",
                          port_name, it->width, sig_width));
        }

        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          // 23.3.2.3: the implicit .name form escalates to an error precisely
          // in the cases where the equivalent explicit named connection would
          // merely warn (23.3.3.7). Net types that are equivalent (for example
          // the wire/tri aliases) are not dissimilar, so they neither warn nor
          // error here.
          if (snet != NetType::kNone && snet != NetType::kInterconnect &&
              !it->is_interconnect &&
              DissimilarNetTypeRequiresWarning(pnet, snet)) {
            diag_.Error(
                item->loc,
                std::format("implicit named port connection '.{}' between "
                            "dissimilar net types",
                            port_name));
          }
        }
      }

      if (!is_implicit && conn_expr &&
          conn_expr->kind == ExprKind::kIdentifier) {
        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          if (snet != NetType::kNone && snet != pnet) {
            if (DissimilarNetTypeRequiresWarning(pnet, snet)) {
              diag_.Warning(
                  item->loc,
                  std::format("port '{}' connected between dissimilar "
                              "net types",
                              binding.port_name));
            }
          }
        }
      }
    }

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        it != child_ports.end() && !it->is_interface_port) {
      DataTypeKind port_kind = NormalizeForCompatibility(it->type_kind);
      if (port_kind != DataTypeKind::kImplicit) {
        DataTypeKind sig_kind = DataTypeKind::kImplicit;
        auto vt = var_types_.find(conn_expr->text);
        if (vt != var_types_.end()) {
          sig_kind = NormalizeForCompatibility(vt->second);
        } else if (net_names_.count(conn_expr->text)) {
          sig_kind = DataTypeKind::kLogic;
        }
        if (sig_kind != DataTypeKind::kImplicit) {
          DataType port_dt{};
          port_dt.kind = port_kind;
          DataType sig_dt{};
          sig_dt.kind = sig_kind;
          if (!IsAssignmentCompatible(sig_dt, port_dt)) {
            diag_.Error(item->loc,
                        std::format("port connection type is not assignment "
                                    "compatible with port '{}'",
                                    binding.port_name));
          }
        }
      }

      if (it->direction == Direction::kInout &&
          nettype_net_names_.count(conn_expr->text)) {
        diag_.Error(
            item->loc,
            std::format("user-defined nettype signal '{}' cannot connect "
                        "to inout port '{}'",
                        conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kInout &&
          var_types_.count(conn_expr->text) &&
          net_names_.count(conn_expr->text) == 0) {
        diag_.Error(item->loc,
                    std::format("variable '{}' cannot be connected to "
                                "inout port '{}'",
                                conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kRef &&
          net_names_.count(conn_expr->text)) {
        diag_.Error(item->loc,
                    std::format("net '{}' cannot be connected to ref port "
                                "'{}'; ref port requires a variable",
                                conn_expr->text, binding.port_name));
      }

      if (it->is_var && connects_to_interconnect(conn_expr->text)) {
        diag_.Error(item->loc,
                    std::format("port variable '{}' cannot be connected to "
                                "interconnect '{}'",
                                binding.port_name, conn_expr->text));
      }
    }

    if (conn_expr && binding.direction != Direction::kInput) {
      std::function<bool(const Expr*)> has_rep = [&](const Expr* e) -> bool {
        if (!e) return false;
        if (e->kind == ExprKind::kReplicate) return true;
        if (e->kind == ExprKind::kConcatenation) {
          for (const auto* el : e->elements)
            if (has_rep(el)) return true;
        }
        return false;
      };
      if (has_rep(conn_expr)) {
        diag_.Error(conn_expr->range.start,
                    "replication shall not appear in an output or inout "
                    "port connection");
      }
    }

    if (conn_expr) {
      bool is_pattern = conn_expr->kind == ExprKind::kAssignmentPattern ||
                        (conn_expr->kind == ExprKind::kCast && conn_expr->lhs &&
                         conn_expr->lhs->kind == ExprKind::kAssignmentPattern);
      if (is_pattern) {
        diag_.Error(conn_expr->range.start,
                    "assignment pattern expression shall not be used in a "
                    "port expression");
      }
    }

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        binding.direction != Direction::kInput &&
        net_names_.count(conn_expr->text) == 0) {
      auto name = conn_expr->text;
      if (!output_port_targets_.emplace(name, item->loc).second) {
        diag_.Error(
            item->loc,
            std::format("variable '{}' driven by multiple outputs", name));
      }
    }

    if (is_ordered && !binding.connection &&
        binding.direction == Direction::kInput && it != child_ports.end() &&
        it->default_value) {
      binding.connection = it->default_value;
    }

    if (has_pull && !binding.connection &&
        binding.direction == Direction::kInput) {
      binding.connection = MakePullExpr(unit_->unconnected_drive);
    }

    if (!binding.connection && binding.direction == Direction::kInput &&
        it != child_ports.end() && !it->is_var &&
        PortNetType(it->type_kind) != NetType::kNone) {
      binding.connection = MakeHighZExpr();
    }

    // §25.5: a modport may be selected in the module header for an interface
    // port (e.g. `iface.target a`) and again in the instance connection
    // (`.a(inst.initiator)`). When both sites select one, they shall name the
    // same modport. Only the genuine both-specified case is checked: a bare
    // instance reference in the connection, or a header port without a modport,
    // leaves nothing to disagree about.
    if (it != child_ports.end() && it->is_interface_port && conn_expr &&
        conn_expr->kind == ExprKind::kMemberAccess && conn_expr->lhs &&
        conn_expr->lhs->kind == ExprKind::kIdentifier && conn_expr->rhs &&
        conn_expr->rhs->kind == ExprKind::kIdentifier) {
      std::string_view header_modport;
      if (const auto* child_decl = FindModule(inst.module_name)) {
        for (const auto& p : child_decl->ports) {
          if (p.name == binding.port_name) {
            header_modport = p.data_type.modport_name;
            break;
          }
        }
      }
      auto connection_modport = conn_expr->rhs->text;
      if (!header_modport.empty() && !connection_modport.empty() &&
          header_modport != connection_modport) {
        diag_.Error(
            item->loc,
            std::format("interface port '{}' selects modport '{}' in the module "
                        "header but '{}' in the instance connection; both shall "
                        "name the same modport",
                        binding.port_name, header_modport, connection_modport));
      }
    }

    inst.port_bindings.push_back(binding);
  }

  if (item->inst_wildcard) {
    for (const auto& port : child_ports) {
      bool connected = false;
      for (const auto& [pname, _] : item->inst_ports) {
        if (pname == port.name) {
          connected = true;
          break;
        }
      }
      if (connected) continue;

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.is_interface_port) {
        if (port.interface_type_name.empty()) {
          diag_.Error(
              item->loc,
              std::format("implicit .* port connection cannot reference "
                          "generic interface port '{}' of module '{}'",
                          port.name, inst.module_name));
        } else if (interface_inst_types_.count(port.name)) {
          auto* expr = arena_.Create<Expr>();
          expr->kind = ExprKind::kIdentifier;
          expr->text = port.name;
          binding.connection = expr;
        }
      } else if (IsNameDeclared(port.name, parent_mod)) {
        uint32_t sig_width = FindSignalWidth(port.name, parent_mod);
        if (sig_width != 0 && sig_width != port.width) {
          diag_.Error(item->loc,
                      std::format("implicit .* port connection '.{}' requires "
                                  "equivalent data types (port width {}, "
                                  "signal width {})",
                                  port.name, port.width, sig_width));
        }

        NetType pnet = PortNetType(port.type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(port.name, parent_mod);
          if (snet != NetType::kNone && snet != pnet &&
              snet != NetType::kInterconnect && !port.is_interconnect) {
            diag_.Error(item->loc,
                        std::format("implicit .* port connection '.{}' between "
                                    "dissimilar net types",
                                    port.name));
          }
        }

        if (port.direction == Direction::kInout &&
            nettype_net_names_.count(port.name)) {
          diag_.Error(
              item->loc,
              std::format("user-defined nettype signal '{}' cannot connect "
                          "to inout port '{}'",
                          port.name, port.name));
        }

        if (port.direction == Direction::kInout &&
            var_types_.count(port.name) && net_names_.count(port.name) == 0) {
          diag_.Error(item->loc,
                      std::format("variable '{}' cannot be connected to "
                                  "inout port '{}'",
                                  port.name, port.name));
        }

        if (port.direction == Direction::kRef && net_names_.count(port.name)) {
          diag_.Error(item->loc,
                      std::format("net '{}' cannot be connected to ref port "
                                  "'{}'; ref port requires a variable",
                                  port.name, port.name));
        }

        if (port.is_var && connects_to_interconnect(port.name)) {
          diag_.Error(item->loc,
                      std::format("port variable '{}' cannot be connected to "
                                  "interconnect '{}'",
                                  port.name, port.name));
        }

        auto* expr = arena_.Create<Expr>();
        expr->kind = ExprKind::kIdentifier;
        expr->text = port.name;
        binding.connection = expr;

        if (binding.direction != Direction::kInput &&
            net_names_.count(port.name) == 0) {
          if (!output_port_targets_.emplace(port.name, item->loc).second) {
            diag_.Error(item->loc,
                        std::format("variable '{}' driven by multiple outputs",
                                    port.name));
          }
        }
      } else if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull && port.direction == Direction::kInput) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (port.direction == Direction::kInput && !port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  } else {
    size_t first_unconnected = is_ordered ? item->inst_ports.size() : 0;
    for (size_t i = first_unconnected; i < child_ports.size(); ++i) {
      const auto& port = child_ports[i];
      if (port.direction != Direction::kInput) continue;

      if (!is_ordered) {
        bool connected = false;
        for (const auto& [pname, _] : item->inst_ports) {
          if (pname == port.name) {
            connected = true;
            break;
          }
        }
        if (connected) continue;
      }

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (!port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  }

  for (const auto& port : child_ports) {
    if (port.direction != Direction::kRef) continue;
    bool connected = false;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name && binding.connection) {
        connected = true;
        break;
      }
    }
    if (!connected) {
      diag_.Error(item->loc,
                  std::format("ref port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
    }
  }

  for (const auto& port : child_ports) {
    if (!port.is_interface_port) continue;

    Expr* conn = nullptr;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name) {
        conn = binding.connection;
        break;
      }
    }

    if (!conn) {
      diag_.Error(item->loc,
                  std::format("interface port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
      continue;
    }

    std::string_view conn_name;
    if (conn->kind == ExprKind::kIdentifier) {
      conn_name = conn->text;
    } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
               conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
               conn->rhs->kind == ExprKind::kIdentifier) {
      conn_name = conn->lhs->text;
    } else {
      diag_.Error(item->loc,
                  std::format("interface port '{}' must be connected to an "
                              "interface instance or interface port",
                              port.name));
      continue;
    }

    std::string_view conn_ifc_type;

    auto iit = interface_inst_types_.find(conn_name);
    if (iit != interface_inst_types_.end()) {
      conn_ifc_type = iit->second;
    } else {
      bool is_ifc_port = false;
      for (const auto& pp : parent_mod->ports) {
        if (pp.name == conn_name && pp.is_interface_port) {
          conn_ifc_type = pp.interface_type_name;
          is_ifc_port = true;
          break;
        }
      }
      if (!is_ifc_port) {
        diag_.Error(item->loc,
                    std::format("interface port '{}' must be connected to an "
                                "interface instance or interface port",
                                port.name));
        continue;
      }
    }

    if (!port.interface_type_name.empty() && !conn_ifc_type.empty() &&
        port.interface_type_name != conn_ifc_type) {
      diag_.Error(
          item->loc,
          std::format("interface port '{}' requires interface type '{}' "
                      "but is connected to instance of type '{}'",
                      port.name, port.interface_type_name, conn_ifc_type));
    }
  }
}

void Elaborator::CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc) {
  if (!inst.resolved) return;

  std::unordered_set<std::string_view> child_assign_targets;
  for (const auto& ca : inst.resolved->assigns) {
    if (ca.lhs && ca.lhs->kind == ExprKind::kIdentifier)
      child_assign_targets.insert(ca.lhs->text);
  }

  for (const auto& binding : inst.port_bindings) {
    if (binding.direction == Direction::kInput &&
        child_assign_targets.count(binding.port_name)) {
      diag_.Warning(loc,
                    std::format("port '{}' is declared as input but is driven "
                                "inside module '{}'",
                                binding.port_name, inst.module_name));
    }

    if (binding.direction == Direction::kOutput && binding.connection &&
        binding.connection->kind == ExprKind::kIdentifier &&
        cont_assign_targets_.count(binding.connection->text)) {
      diag_.Warning(
          loc, std::format("port '{}' is declared as output but its connection "
                           "'{}' is also driven externally",
                           binding.port_name, binding.connection->text));
    }
  }
}

void Elaborator::CheckUwirePortMerge(const RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    NetType internal_net = PortNetType(port_it->type_kind);
    bool internal_is_uwire = (internal_net == NetType::kUwire);

    bool external_is_net = false;
    bool external_is_uwire = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      NetType ext = FindSignalNetType(binding.connection->text, parent_mod);
      external_is_net = (ext != NetType::kNone);
      external_is_uwire = (ext == NetType::kUwire);
    }

    if (!internal_is_uwire && !external_is_uwire) continue;

    bool merged = (internal_net != NetType::kNone) && external_is_net;
    if (!merged) {
      diag_.Warning(
          item->loc,
          std::format("uwire net on port '{}' of instance '{}' is not "
                      "merged into a single net",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::CheckInterconnectPortMerge(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    bool internal_is_interconnect = port_it->is_interconnect;

    bool external_is_interconnect = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      external_is_interconnect =
          interconnect_names_.count(binding.connection->text) != 0;
    }

    if (internal_is_interconnect && external_is_interconnect) {
      diag_.Error(
          item->loc,
          std::format("simulated net for port '{}' of instance '{}' has "
                      "interconnect type at end of elaboration",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::ResolveInterconnectPrimitiveTerminals(
    const std::vector<Expr*>& terminals, RtlirModule* mod) {
  for (const auto* term : terminals) {
    if (!term || term->kind != ExprKind::kIdentifier) continue;
    if (interconnect_names_.count(term->text) == 0) continue;
    auto scoped = ScopedName(term->text);
    for (auto& net : mod->nets) {
      if (net.name == scoped && net.net_type == NetType::kInterconnect) {
        net.net_type = NetType::kWire;
        break;
      }
    }
    interconnect_names_.erase(term->text);
  }
}

void Elaborator::ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;
    if (port_it->num_unpacked_dims == 0) continue;

    if (!binding.connection ||
        binding.connection->kind != ExprKind::kIdentifier) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    auto it = var_array_info_.find(binding.connection->text);
    if (it == var_array_info_.end()) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    const auto& conn_info = it->second;
    if (conn_info.num_unpacked_dims != port_it->num_unpacked_dims) {
      diag_.Error(
          item->loc,
          std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                      "but connection has {}",
                      binding.port_name, port_it->num_unpacked_dims,
                      conn_info.num_unpacked_dims));
      continue;
    }

    for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
      if (d < port_it->unpacked_dim_sizes.size() &&
          d < conn_info.dim_sizes.size() &&
          port_it->unpacked_dim_sizes[d] != conn_info.dim_sizes[d]) {
        diag_.Error(
            item->loc,
            std::format("unpacked array port '{}' dimension {} has size {} "
                        "but connection has size {}",
                        binding.port_name, d, port_it->unpacked_dim_sizes[d],
                        conn_info.dim_sizes[d]));
        break;
      }
    }
  }
}

void Elaborator::ValidateInstanceArrayPorts(
    const RtlirModuleInst& inst, const ModuleItem* item,
    RtlirModule* parent_mod, const std::vector<uint32_t>& inst_dim_sizes,
    uint32_t total_instances) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    bool conn_is_unpacked = false;
    uint32_t conn_num_dims = 0;
    const std::vector<uint32_t>* conn_dim_sizes_ptr = nullptr;
    uint32_t conn_width = 0;

    if (binding.connection->kind == ExprKind::kIdentifier) {
      auto it = var_array_info_.find(binding.connection->text);
      if (it != var_array_info_.end()) {
        conn_is_unpacked = true;
        conn_num_dims = it->second.num_unpacked_dims;
        conn_dim_sizes_ptr = &it->second.dim_sizes;
      }
      conn_width = FindSignalWidth(binding.connection->text, parent_mod);
    }

    if (conn_is_unpacked) {
      uint32_t expected_dims = static_cast<uint32_t>(inst_dim_sizes.size()) +
                               port_it->num_unpacked_dims;
      if (conn_num_dims != expected_dims) {
        diag_.Error(
            item->loc,
            std::format("unpacked array connection to port '{}' has {} "
                        "dimension(s) but expected {}",
                        binding.port_name, conn_num_dims, expected_dims));
        continue;
      }
      if (conn_dim_sizes_ptr) {
        for (size_t d = 0; d < inst_dim_sizes.size(); ++d) {
          if (d < conn_dim_sizes_ptr->size() &&
              (*conn_dim_sizes_ptr)[d] != inst_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "dimension {} has size {} but instance array "
                            "has size {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[d],
                            inst_dim_sizes[d]));
            break;
          }
        }
        for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
          uint32_t ci = static_cast<uint32_t>(inst_dim_sizes.size()) + d;
          if (ci < conn_dim_sizes_ptr->size() &&
              d < port_it->unpacked_dim_sizes.size() &&
              (*conn_dim_sizes_ptr)[ci] != port_it->unpacked_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "port dimension {} has size {} but port "
                            "expects {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[ci],
                            port_it->unpacked_dim_sizes[d]));
            break;
          }
        }
      }
    } else if (conn_width != 0 && conn_width != port_it->width) {
      uint32_t expected_width = port_it->width * total_instances;
      if (conn_width != expected_width) {
        diag_.Error(
            item->loc,
            std::format("packed array connection to port '{}' has width {} "
                        "but expected {} ({} instances * port width {})",
                        binding.port_name, conn_width, expected_width,
                        total_instances, port_it->width));
      }
    }
  }
}

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) const {
  ScopeMap scope = cu_param_scope_;
  for (const auto& p : mod->params) {
    if (p.is_resolved) {
      scope[p.name] = p.resolved_value;
    }
  }
  return scope;
}

bool Elaborator::RefersToUnboundedParam(const RtlirModule* mod,
                                        std::string_view name) const {
  for (const auto& p : mod->params) {
    if (p.is_unbounded && p.name == name) return true;
  }
  return false;
}

bool Elaborator::ContainsDollarSubexpr(const Expr* e) const {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "$") return true;
  if (ContainsDollarSubexpr(e->lhs)) return true;
  if (ContainsDollarSubexpr(e->rhs)) return true;
  if (ContainsDollarSubexpr(e->condition)) return true;
  if (ContainsDollarSubexpr(e->true_expr)) return true;
  if (ContainsDollarSubexpr(e->false_expr)) return true;
  if (ContainsDollarSubexpr(e->base)) return true;
  if (ContainsDollarSubexpr(e->index)) return true;
  if (ContainsDollarSubexpr(e->index_end)) return true;
  if (ContainsDollarSubexpr(e->with_expr)) return true;
  if (ContainsDollarSubexpr(e->repeat_count)) return true;
  for (const Expr* a : e->args)
    if (ContainsDollarSubexpr(a)) return true;
  for (const Expr* el : e->elements)
    if (ContainsDollarSubexpr(el)) return true;
  return false;
}

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

std::string_view Elaborator::ScopedName(std::string_view base) {
  if (gen_prefix_.empty()) return base;
  std::string full = gen_prefix_ + std::string(base);
  return {arena_.AllocString(full.c_str(), full.size()), full.size()};
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
