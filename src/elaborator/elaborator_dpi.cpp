#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_dpi_formals.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/elaborator_dpi_signature.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/let_construct.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser_dpi_validate.h"

namespace delta {

void Elaborator::ValidateDpiImport(const ModuleItem* item) {
  if (!item->dpi_is_pure) return;

  if (item->dpi_is_task) {
    diag_.Error(item->loc, "imported task cannot be declared pure",
                Subclause("35.5.2"));
    return;
  }
  if (item->return_type.kind == DataTypeKind::kVoid) {
    diag_.Error(item->loc,
                "pure imported function must have a non-void return type",
                Subclause("35.5.2"));
  }

  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kOutput ||
        arg.direction == Direction::kInout) {
      diag_.Error(item->loc,
                  "pure imported function cannot have output or inout "
                  "arguments",
                  Subclause("35.5.2"));
      break;
    }
  }
}

namespace {

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

void CheckDuplicateImportNamesInScope(const std::vector<ModuleItem*>& items,
                                      DiagEngine& diag) {
  std::unordered_set<std::string_view> sv_names_in_scope;
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind != ModuleItemKind::kDpiImport) continue;
    auto [it, inserted] = sv_names_in_scope.insert(item->name);
    if (!inserted) {
      diag.Error(
          item->loc,
          std::format("DPI import name '{}' already declared in this scope",
                      item->name),
          Subclause("35.5.4"));
    }
  }
}

std::string_view ExportedSubroutineKind(const ModuleItem* callable) {
  return callable->kind == ModuleItemKind::kTaskDecl ? "task" : "function";
}

void CheckExportRefArguments(const ModuleItem* callable, const ModuleItem* item,
                             DiagEngine& diag) {
  for (const auto& arg : callable->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error(item->loc,
                 std::format("SystemVerilog {} '{}' has a ref argument "
                             "and therefore cannot be exported",
                             ExportedSubroutineKind(callable), item->name),
                 Subclause("35.7"));
      break;
    }
  }
}

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
                 std::format("SystemVerilog {} '{}' has a dynamic array "
                             "formal argument and therefore cannot be exported "
                             "for DPI",
                             ExportedSubroutineKind(callable), item->name),
                 Subclause("35.5.6"));
      break;
    }
  }
}

void CheckImportResultTypedefType(const ModuleItem* item,
                                  const TypedefMap& typedefs,
                                  const DpiClassNames& classes,
                                  DiagEngine& diag) {
  if (item->dpi_is_task) return;
  if (item->return_type.kind != DataTypeKind::kNamed) return;
  if (NamesAClass(item->return_type, typedefs, classes)) {
    diag.Error(item->loc,
               std::format("imported function '{}' has a class type as its "
                           "result, which cannot be passed through the DPI",
                           item->name),
               Subclause("35.5.5"));
    return;
  }
  DataType resolved = ResolveDpiTypeName(item->return_type, typedefs);
  if (resolved.kind == DataTypeKind::kNamed) return;
  if (IsPermittedDpiResultType(resolved)) return;
  diag.Error(
      item->loc,
      std::format("imported function '{}' has result type '{}', which is not "
                  "permitted for DPI; function results are restricted to small "
                  "values",
                  item->name, item->return_type.type_name),
      Subclause("35.5.5"));
}

void CheckExportFormalTypes(const ModuleItem* callable, const ModuleItem* item,
                            const TypedefMap& typedefs,
                            const DpiClassNames& classes, DiagEngine& diag) {
  for (const auto& arg : callable->func_args) {
    if (NamesAClass(arg.data_type, typedefs, classes)) {
      diag.Error(
          item->loc,
          std::format("SystemVerilog {} '{}' has a formal argument '{}' of a "
                      "class type, which cannot be passed through the DPI",
                      ExportedSubroutineKind(callable), item->name, arg.name),
          Subclause("35.5.4"));
      continue;
    }
    DpiFormalTypeVerdict verdict =
        ClassifyDpiFormalType(ResolveDpiTypeName(arg.data_type, typedefs));
    if (verdict == DpiFormalTypeVerdict::kPermitted) continue;
    if (verdict == DpiFormalTypeVerdict::kUnpackedUnion) {
      diag.Error(
          item->loc,
          std::format("SystemVerilog {} '{}' has an unpacked union formal "
                      "argument '{}'; only the packed form of a union is "
                      "permitted for DPI",
                      ExportedSubroutineKind(callable), item->name, arg.name),
          Subclause("35.5.6"));
    } else {
      diag.Error(
          item->loc,
          std::format("SystemVerilog {} '{}' has a formal argument '{}' whose "
                      "type is not permitted for DPI",
                      ExportedSubroutineKind(callable), item->name, arg.name),
          Subclause("35.5.6"));
    }
    break;
  }
}

void CheckExportResultType(const ModuleItem* callable, const ModuleItem* item,
                           const TypedefMap& typedefs, DiagEngine& diag) {
  if (callable->kind == ModuleItemKind::kFunctionDecl &&
      !IsPermittedDpiResultType(
          ResolveDpiTypeName(callable->return_type, typedefs))) {
    diag.Error(item->loc,
               std::format("exported function '{}' has a result type that is "
                           "not permitted for DPI; function results are "
                           "restricted to small values",
                           item->name),
               Subclause("35.5.5"));
  }
}

void CheckExportSignatureEquivalence(
    const DpiExportSignature& sig, std::string_view link_name,
    const ModuleItem* item,
    std::unordered_map<std::string_view, DpiExportSignature>& export_signatures,
    DiagEngine& diag) {
  auto [sig_it, sig_was_new] = export_signatures.emplace(link_name, sig);
  if (!sig_was_new && !(sig_it->second == sig)) {
    diag.Error(item->loc,
               std::format("DPI export linkage name '{}' was previously "
                           "declared with a different type signature; "
                           "exports sharing one linkage name across scopes "
                           "must have equivalent signatures",
                           link_name),
               Subclause("35.4"));
  }
}

void CheckExportDuplicateLinkName(
    const ModuleItem* item, std::string_view link_name,
    std::unordered_set<std::string_view>& export_link_in_scope,
    DiagEngine& diag) {
  auto [_, inserted] = export_link_in_scope.insert(link_name);
  if (!inserted) {
    diag.Error(item->loc,
               std::format("DPI export linkage name '{}' already declared in "
                           "this scope",
                           link_name),
               Subclause("35.4"));
  }
}

void CheckExportDuplicateSvFunc(
    const ModuleItem* item,
    std::unordered_set<std::string_view>& exported_sv_func_in_scope,
    DiagEngine& diag) {
  auto [_func, func_inserted] = exported_sv_func_in_scope.insert(item->name);
  if (!func_inserted) {
    std::string_view kind = item->dpi_is_task ? "task" : "function";
    diag.Error(item->loc,
               std::format("SystemVerilog {} '{}' is already exported in this "
                           "scope; only one export declaration per {} is "
                           "permitted",
                           kind, item->name, kind),
               Subclause("35.7"));
  }
}

struct ExportScopeContext {
  const std::unordered_map<std::string_view, const ModuleItem*>& sv_callables;
  std::unordered_set<std::string_view>& export_link_in_scope;
  std::unordered_set<std::string_view>& exported_sv_func_in_scope;
  const TypedefMap& typedefs;
  const DpiClassNames& classes;
};

void ValidateExportDeclaration(
    const ModuleItem* item, std::string_view link_name,
    ExportScopeContext& scope,
    std::unordered_map<std::string_view, DpiExportSignature>& export_signatures,
    DiagEngine& diag) {
  CheckExportDuplicateLinkName(item, link_name, scope.export_link_in_scope,
                               diag);
  CheckExportDuplicateSvFunc(item, scope.exported_sv_func_in_scope, diag);

  auto callable_it = scope.sv_callables.find(item->name);
  if (callable_it == scope.sv_callables.end()) {
    diag.Error(item->loc,
               std::format("DPI export names '{}', which is not a "
                           "SystemVerilog function or task defined in the "
                           "enclosing scope",
                           item->name),
               Subclause("35.7"));
    return;
  }

  const ModuleItem* callable = callable_it->second;
  if (!callable->method_class.empty()) {
    diag.Error(
        item->loc,
        std::format("SystemVerilog {} '{}' is a member of class '{}' and class "
                    "member functions cannot be exported",
                    ExportedSubroutineKind(callable), item->name,
                    callable->method_class),
        Subclause("35.7"));
    return;
  }
  if (item->dpi_is_task != (callable->kind == ModuleItemKind::kTaskDecl)) {
    diag.Error(item->loc,
               std::format("DPI export declares '{}' with the '{}' keyword, "
                           "but '{}' is a SystemVerilog {}",
                           item->name, item->dpi_is_task ? "task" : "function",
                           item->name, ExportedSubroutineKind(callable)),
               Subclause("35.8"));
    return;
  }
  CheckExportRefArguments(callable, item, diag);
  CheckExportDynamicArrayArguments(callable, item, diag);
  CheckExportFormalTypes(callable, item, scope.typedefs, scope.classes, diag);
  CheckExportFormalUnpackedDims(callable, item, scope.typedefs, scope.classes,
                                diag);
  CheckExportResultType(callable, item, scope.typedefs, diag);
  CheckExportSignatureEquivalence(
      BuildDpiExportSignature(callable, scope.typedefs), link_name, item,
      export_signatures, diag);
}

void CheckImportSignatureAgreement(
    const ModuleItem* item, const TypedefMap& typedefs,
    std::unordered_map<std::string_view, DpiSignatureKey>& signatures,
    std::unordered_map<std::string_view, SourceLoc>& first_decl_loc,
    DiagEngine& diag) {
  auto link_name = DpiLinkageName(item);
  auto sig = BuildDpiSignature(item, typedefs);

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
                    link_name),
        Subclause("35.5.4"));
  }
}

std::unordered_map<std::string_view, const ModuleItem*> IndexSvCallables(
    const std::vector<ModuleItem*>& items) {
  std::unordered_map<std::string_view, const ModuleItem*> sv_callables;
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      sv_callables.emplace(item->name, item);
    }
  }
  return sv_callables;
}

void CheckDpiVersionStringAgreement(
    const ModuleItem* item, std::string_view link_name,
    std::unordered_map<std::string_view, std::string_view>& link_version,
    DiagEngine& diag) {
  auto found = link_version.find(link_name);
  if (found == link_version.end()) {
    link_version.emplace(link_name, item->dpi_spec_string);
    return;
  }
  if (found->second != item->dpi_spec_string) {
    diag.Error(
        item->loc,
        std::format("DPI linkage name '{}' was previously declared with "
                    "version string \"{}\"; all declarations sharing one "
                    "linkage name must use the same version string",
                    link_name, found->second),
        Subclause("35.4"));
  }
}

struct DpiGlobalNameSpace {
  std::unordered_map<std::string_view, std::string_view>& link_version;
  std::unordered_map<std::string_view, DpiExportSignature>& export_signatures;
};

void ProcessDpiGlobalNameItem(const ModuleItem* item, ExportScopeContext& scope,
                              DpiGlobalNameSpace& global, DiagEngine& diag) {
  auto link_name = DpiLinkageName(item);

  if (item->kind == ModuleItemKind::kDpiExport) {
    ValidateExportDeclaration(item, link_name, scope, global.export_signatures,
                              diag);
  }

  if (item->kind == ModuleItemKind::kDpiImport) {
    CheckImportFormalTypedefTypes(item, scope.typedefs, scope.classes, diag);
    CheckImportFormalUnpackedDims(item, scope.typedefs, scope.classes, diag);
    CheckImportResultTypedefType(item, scope.typedefs, scope.classes, diag);
  }

  CheckDpiVersionStringAgreement(item, link_name, global.link_version, diag);
}

void CheckDpiScopeImportDeclarations(
    const std::vector<ModuleItem*>& items, const TypedefMap& typedefs,
    std::unordered_map<std::string_view, DpiSignatureKey>& signatures,
    std::unordered_map<std::string_view, SourceLoc>& first_decl_loc,
    DiagEngine& diag) {
  CheckDuplicateImportNamesInScope(items, diag);

  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind != ModuleItemKind::kDpiImport) continue;
    CheckImportSignatureAgreement(item, typedefs, signatures, first_decl_loc,
                                  diag);
  }
}

struct DpiNameContext {
  const CompilationUnit* unit;
  const TypedefMap& typedefs;
  const DpiClassNames& classes;
};

void ProcessDpiScopeItems(const std::vector<ModuleItem*>& items,
                          ExportScopeContext& scope, DpiGlobalNameSpace& global,
                          DiagEngine& diag) {
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind != ModuleItemKind::kDpiImport &&
        item->kind != ModuleItemKind::kDpiExport) {
      continue;
    }
    ProcessDpiGlobalNameItem(item, scope, global, diag);
  }
}

void ValidateDpiScopeGlobalNames(const std::vector<ModuleItem*>& items,
                                 const DpiNameContext& names,
                                 DpiGlobalNameSpace& global, DiagEngine& diag) {
  std::unordered_map<std::string_view, const ModuleItem*> sv_callables =
      IndexSvCallables(items);

  TypedefMap dpi_typedefs = DpiScopeTypedefs(items, names.unit, names.typedefs);

  std::unordered_set<std::string_view> export_link_in_scope;
  std::unordered_set<std::string_view> exported_sv_func_in_scope;

  ExportScopeContext scope{sv_callables, export_link_in_scope,
                           exported_sv_func_in_scope, dpi_typedefs,
                           names.classes};

  ProcessDpiScopeItems(items, scope, global, diag);
}

void AddGenerateScopes(const std::vector<ModuleItem*>& items,
                       std::vector<const std::vector<ModuleItem*>*>& scopes) {
  for (const auto* item : items) {
    if (item == nullptr || item->gen_body.empty()) continue;
    scopes.push_back(&item->gen_body);
    AddGenerateScopes(item->gen_body, scopes);
  }
}

std::vector<const std::vector<ModuleItem*>*> DpiDeclarationScopes(
    const CompilationUnit* unit,
    const std::vector<CompilationUnit*>& separate_units) {
  std::vector<const std::vector<ModuleItem*>*> scopes;
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      if (decl != nullptr) scopes.push_back(&decl->items);
    }
  }
  for (const auto* pkg : unit->packages) {
    if (pkg != nullptr) scopes.push_back(&pkg->items);
  }
  if (separate_units.empty()) scopes.push_back(&unit->cu_items);
  for (const auto* own : separate_units) scopes.push_back(&own->cu_items);
  size_t direct_scopes = scopes.size();
  for (size_t k = 0; k < direct_scopes; ++k) {
    AddGenerateScopes(*scopes[k], scopes);
  }
  return scopes;
}

}  // namespace

void Elaborator::ValidateDpiDeclarations() {
  if (unit_ == nullptr) return;

  std::unordered_map<std::string_view, DpiSignatureKey> signatures;
  std::unordered_map<std::string_view, SourceLoc> first_decl_loc;

  for (const auto* items : DpiDeclarationScopes(unit_, units_.units)) {
    CheckDpiScopeImportDeclarations(*items,
                                    DpiScopeTypedefs(*items, unit_, typedefs_),
                                    signatures, first_decl_loc, diag_);
  }
}

void Elaborator::ValidateDpiGlobalNameSpace() {
  if (unit_ == nullptr) return;

  std::unordered_map<std::string_view, std::string_view> link_version;

  std::unordered_map<std::string_view, DpiExportSignature> export_signatures;

  DpiGlobalNameSpace global{link_version, export_signatures};

  auto scopes = DpiDeclarationScopes(unit_, units_.units);
  DpiClassNames classes = CollectDpiClassNames(unit_, scopes);

  DpiNameContext names{unit_, typedefs_, classes};

  for (const auto* items : scopes) {
    ValidateDpiScopeGlobalNames(*items, names, global, diag_);
  }
}

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
      return LetFormalTypeKind::kAssertionExpressionType;
  }
}

static void ReportEventFormalRefs(
    const Expr* e, const std::unordered_set<std::string_view>& events,
    DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier && events.contains(e->text)) {
    diag.Error(e->range.start,
               std::format("event formal '{}' of a let is referenced where no "
                           "event_expression may be written",
                           e->text),
               Subclause("11.12"));
  }
  ForEachExprChild(e, [&events, &diag](const Expr* child) {
    ReportEventFormalRefs(child, events, diag);
  });
}

void Elaborator::ElaborateLetFormals(ModuleItem* item, const RtlirModule* mod) {
  for (auto& arg : item->func_args) {
    if (mod != nullptr) ResolveTypeRef(arg.data_type, item->loc, mod);
    LetFormalTypeKind kind = ClassifyLetFormalType(arg.data_type);
    if (!IsLetFormalTypeAllowed(kind)) {
      diag_.Error(item->loc,
                  std::format("let formal argument '{}' must be of type event "
                              "or a type allowed in a Boolean expression",
                              arg.name),
                  Subclause("11.12"));
    }
  }
  std::unordered_set<std::string_view> events;
  const std::vector<const DataType*> kTypes = LetFormalTypes(item->func_args);
  for (size_t i = 0; i < kTypes.size(); ++i) {
    if (kTypes[i] != nullptr && kTypes[i]->kind == DataTypeKind::kEvent)
      events.insert(item->func_args[i].name);
  }
  ReportEventFormalRefs(item->init_expr, events, diag_);
}

}  // namespace delta
