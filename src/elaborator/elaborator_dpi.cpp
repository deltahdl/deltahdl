#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/let_construct.h"
#include "elaborator/rtlir.h"
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

// §35.5.4: "multiple imports of the same subroutine name into the same scope
// are forbidden." We treat each module declaration as one scope, so this scans
// a single module's items for repeated DPI import subroutine names.
void CheckDuplicateImportNamesInScope(const ModuleDecl* mod, DiagEngine& diag) {
  std::unordered_set<std::string_view> sv_names_in_scope;
  for (const auto* item : mod->items) {
    if (item == nullptr) continue;
    if (item->kind != ModuleItemKind::kDpiImport) continue;
    auto [it, inserted] = sv_names_in_scope.insert(item->name);
    if (!inserted) {
      diag.Error(
          item->loc,
          std::format("DPI import name '{}' already declared in this scope",
                      item->name));
    }
  }
}

// §35.7: an exported function adheres to the same restrictions on argument
// types as imports. The §35.5.4 prohibition on the ref qualifier in a DPI
// declaration therefore carries through to the exported routine's formal
// arguments.
void CheckExportRefArguments(const ModuleItem* callable, const ModuleItem* item,
                             DiagEngine& diag) {
  for (const auto& arg : callable->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error(item->loc,
                 std::format("SystemVerilog function '{}' has a ref argument "
                             "and therefore cannot be exported (§35.7)",
                             item->name));
      break;
    }
  }
}

// §35.5.6: it is erroneous for an exported DPI subroutine to declare a formal
// argument of a dynamic array type. (Unsized "open" array formals are a
// relaxation reserved for imports under §35.5.6.1; exports get no such
// allowance.) A dynamic array shows up as an unpacked dimension with no bounds
// -- the empty-bracket "[]" form, recorded by the parser as a null dimension
// entry. Queues ("[$]"), associative arrays ("[*]" / "[type]") and fixed-size
// unpacked arrays all carry a non-null dimension marker, so they are not
// mistaken for dynamic arrays here.
void CheckExportDynamicArrayArguments(const ModuleItem* callable,
                                      const ModuleItem* item,
                                      DiagEngine& diag) {
  for (const auto& arg : callable->func_args) {
    bool has_dynamic_dim = false;
    for (const Expr* dim : arg.unpacked_dims) {
      if (dim == nullptr) {
        has_dynamic_dim = true;
        break;
      }
    }
    if (has_dynamic_dim) {
      diag.Error(item->loc,
                 std::format("SystemVerilog function '{}' has a dynamic array "
                             "formal argument and therefore cannot be exported "
                             "for DPI (§35.5.6)",
                             item->name));
      break;
    }
  }
}

// §35.5.5: an exported function's result type is subject to the same
// small-value restriction as an imported function's result. Tasks carry no
// result, so the check applies only when the exported routine is a function.
void CheckExportResultType(const ModuleItem* callable, const ModuleItem* item,
                           DiagEngine& diag) {
  if (callable->kind == ModuleItemKind::kFunctionDecl &&
      !IsPermittedDpiResultType(callable->return_type)) {
    diag.Error(item->loc,
               std::format("exported function '{}' has a result type that is "
                           "not permitted for DPI; function results are "
                           "restricted to small values (§35.5.5)",
                           item->name));
  }
}

// §35.4 claim 14: exports sharing one linkage name across scopes must have
// equivalent type signatures. Records the signature the first time the linkage
// name is seen and compares against it on later exports.
void CheckExportSignatureEquivalence(
    const ModuleItem* callable, std::string_view link_name,
    const ModuleItem* item,
    std::unordered_map<std::string_view, DpiExportSignature>& export_signatures,
    DiagEngine& diag) {
  auto sig = BuildDpiExportSignature(callable);
  auto [sig_it, sig_was_new] = export_signatures.emplace(link_name, sig);
  if (!sig_was_new && !(sig_it->second == sig)) {
    diag.Error(item->loc,
               std::format("DPI export linkage name '{}' was previously "
                           "declared with a different type signature; "
                           "exports sharing one linkage name across scopes "
                           "must have equivalent signatures",
                           link_name));
  }
}

// §35.4/§35.7: run the full battery of export-declaration checks for one export
// item, given the SystemVerilog callables indexed for its enclosing scope and
// the per-scope / cross-scope bookkeeping sets.
void ValidateExportDeclaration(
    const ModuleItem* item, std::string_view link_name,
    const std::unordered_map<std::string_view, const ModuleItem*>& sv_callables,
    std::unordered_set<std::string_view>& export_link_in_scope,
    std::unordered_set<std::string_view>& exported_sv_func_in_scope,
    std::unordered_map<std::string_view, DpiExportSignature>& export_signatures,
    DiagEngine& diag) {
  auto [_, inserted] = export_link_in_scope.insert(link_name);
  if (!inserted) {
    diag.Error(item->loc,
               std::format("DPI export linkage name '{}' already declared in "
                           "this scope",
                           link_name));
  }

  // §35.7: at most one export per SystemVerilog function in a scope.
  auto [_func, func_inserted] = exported_sv_func_in_scope.insert(item->name);
  if (!func_inserted) {
    diag.Error(item->loc,
               std::format("SystemVerilog function '{}' is already exported in "
                           "this scope; only one export declaration per "
                           "function is permitted (§35.7)",
                           item->name));
  }

  auto callable_it = sv_callables.find(item->name);
  if (callable_it == sv_callables.end()) {
    // §35.7: an export declaration is allowed only in the scope where the
    // function being exported is defined. If the scope contains no
    // SystemVerilog function or task with the named identifier, the export
    // has nothing to attach to.
    diag.Error(item->loc,
               std::format("DPI export names '{}', which is not a "
                           "SystemVerilog function or task defined in the "
                           "enclosing scope (§35.7)",
                           item->name));
    return;
  }

  const ModuleItem* callable = callable_it->second;
  CheckExportRefArguments(callable, item, diag);
  CheckExportDynamicArrayArguments(callable, item, diag);
  CheckExportResultType(callable, item, diag);
  CheckExportSignatureEquivalence(callable, link_name, item, export_signatures,
                                  diag);
}

// §35.5.4: "all declarations, regardless of scope, shall have exactly the same
// type signature." Compares one import's signature against the first one seen
// under the same linkage name, recording it the first time. Argument names and
// defaults may differ.
void CheckImportSignatureAgreement(
    const ModuleItem* item,
    std::unordered_map<std::string_view, DpiSignatureKey>& signatures,
    std::unordered_map<std::string_view, SourceLoc>& first_decl_loc,
    DiagEngine& diag) {
  auto link_name = DpiLinkageName(item);
  auto sig = BuildDpiSignature(item);

  auto found = signatures.find(link_name);
  if (found == signatures.end()) {
    signatures.emplace(link_name, std::move(sig));
    first_decl_loc[link_name] = item->loc;
    return;
  }
  if (!DpiSignaturesMatch(found->second, sig)) {
    diag.Error(
        item->loc,
        std::format("DPI declaration of linkage name '{}' disagrees with the "
                    "earlier declaration's type signature",
                    link_name));
  }
}

}  // namespace

void Elaborator::ValidateDpiDeclarations() {
  if (unit_ == nullptr) return;

  std::unordered_map<std::string_view, DpiSignatureKey> signatures;
  std::unordered_map<std::string_view, SourceLoc> first_decl_loc;

  for (const auto* mod : unit_->modules) {
    if (mod == nullptr) continue;

    CheckDuplicateImportNamesInScope(mod, diag_);

    for (const auto* item : mod->items) {
      if (item == nullptr) continue;
      // Signature comparison applies to imports only — an export declaration
      // carries no signature in its syntax (the signature comes from the
      // SystemVerilog function being exported).
      if (item->kind != ModuleItemKind::kDpiImport) continue;
      CheckImportSignatureAgreement(item, signatures, first_decl_loc, diag_);
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
        ValidateExportDeclaration(
            item, link_name, sv_callables, export_link_in_scope,
            exported_sv_func_in_scope, export_signatures, diag_);
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

namespace {

// Per §20.10.1, the first argument of $fatal is an optional finish_number that
// must be 0, 1, or 2. Returns the index of the first message-list argument: 1
// when a leading integer literal was consumed as the finish_number, else 0.
size_t CheckFatalFinishNumber(const Expr* expr, bool is_fatal,
                              DiagEngine& diag) {
  if (is_fatal && !expr->args.empty()) {
    auto* first_arg = expr->args[0];
    if (first_arg->kind == ExprKind::kIntegerLiteral) {
      auto val = first_arg->int_val;
      if (val < 0 || val > 2) {
        diag.Error(first_arg->range.start, "finish_number must be 0, 1, or 2");
      }
      return 1;
    }
  }
  return 0;
}

// Per §20.10.1, list_of_arguments may only contain a formatting string and
// constant expressions, including constant function calls.
void CheckElabTaskArgsConstant(const Expr* expr, size_t arg_start,
                               std::string_view name, const ScopeMap& scope,
                               DiagEngine& diag) {
  for (size_t i = arg_start; i < expr->args.size(); ++i) {
    auto* arg = expr->args[i];
    if (!arg) continue;
    if (i == arg_start && arg->kind == ExprKind::kStringLiteral) continue;
    if (arg->kind == ExprKind::kStringLiteral) continue;
    if (!IsConstantExpr(arg, scope)) {
      diag.Error(arg->range.start,
                 std::format("argument to {} must be a constant expression "
                             "(§20.10.1)",
                             name));
    }
  }
}

// Compose the diagnostic scope name: the module name (if any) joined to the
// trailing generate prefix with underscores trimmed, separated by a dot.
std::string BuildElabTaskScopeName(const RtlirModule* mod,
                                   const std::string& gen_prefix) {
  std::string scope_name = mod ? std::string(mod->name) : std::string{};
  if (!gen_prefix.empty()) {
    std::string trimmed = gen_prefix;
    while (!trimmed.empty() && trimmed.back() == '_') trimmed.pop_back();
    if (!trimmed.empty()) {
      if (!scope_name.empty()) scope_name.push_back('.');
      scope_name += trimmed;
    }
  }
  return scope_name;
}

// Map the elaboration system task name flags to the severity label embedded in
// the emitted message.
std::string ElabTaskSeverity(bool is_fatal, bool is_error, bool is_warning) {
  if (is_fatal) return "FATAL";
  if (is_error) return "ERROR";
  if (is_warning) return "WARNING";
  return "INFO";
}

// Extract the optional user message: the leading string-literal argument of the
// message list, with surrounding double quotes stripped.
std::string ExtractElabTaskUserMsg(const Expr* expr, size_t arg_start) {
  std::string user_msg;
  if (arg_start < expr->args.size() &&
      expr->args[arg_start]->kind == ExprKind::kStringLiteral) {
    user_msg = std::string(expr->args[arg_start]->text);
    if (user_msg.size() >= 2 && user_msg.front() == '"' &&
        user_msg.back() == '"') {
      user_msg = user_msg.substr(1, user_msg.size() - 2);
    }
  }
  return user_msg;
}

}  // namespace

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

  size_t arg_start = CheckFatalFinishNumber(expr, is_fatal, diag_);

  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CheckElabTaskArgsConstant(expr, arg_start, name, scope, diag_);

  std::string scope_name = BuildElabTaskScopeName(mod, gen_prefix_);
  std::string severity = ElabTaskSeverity(is_fatal, is_error, is_warning);
  std::string user_msg = ExtractElabTaskUserMsg(expr, arg_start);

  std::string message =
      scope_name.empty() ? std::format("elaboration {}: {}", severity, user_msg)
                         : std::format("elaboration {} in scope '{}': {}",
                                       severity, scope_name, user_msg);

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
      return LetFormalTypeKind::kTypeAllowedIn166;
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

}  // namespace delta
