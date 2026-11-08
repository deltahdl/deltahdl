#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_declared_shape.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_method_contents.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_named_type_kinds.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct SubroutineScope {
  VpiObject* scope;
  std::string key;
  bool automatic;
  const RtlirModule* mod = nullptr;
  std::string params;
  const PackageDecl* package = nullptr;
};

struct SubroutineBuild {
  const RtlirDesign& design;
  SimContext& ctx;
  const VpiAttachBuild& build;
  VpiSubroutineObjects& made;
};

bool IsSubroutine(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kDpiImport;
}

bool IsTask(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kTaskDecl || item.dpi_is_task;
}

void MarkDpi(VpiObject* tf, const ModuleItem& decl) {
  tf->is_dpi = true;
  tf->dpi_export = decl.kind == ModuleItemKind::kDpiExport;
  tf->dpi_pure = decl.dpi_is_pure;
  tf->dpi_context = decl.dpi_is_context;
  tf->is_dpi_c = decl.dpi_spec_string == "DPI-C";
  tf->dpi_c_identifier =
      std::string(decl.dpi_c_name.empty() ? decl.name : decl.dpi_c_name);
}

void MarkDpiExports(VpiObject* scope, const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kDpiExport) continue;
    for (VpiObject* child : scope->children) {
      const bool kTaskFunc =
          child->type == vpiTask || child->type == vpiFunction;
      if (kTaskFunc && child->name == item->name) MarkDpi(child, *item);
    }
  }
}

bool DefinesClassMethod(const RtlirModule& mod, const ModuleItem* item) {
  return std::ranges::any_of(mod.class_decls, [item](const ClassDecl* decl) {
    return decl->name == item->method_class;
  });
}

bool DeclaredInGenerateBlock(const RtlirModule& mod, const ModuleItem* item) {
  return std::ranges::any_of(
      mod.gen_block_subroutines,
      [item](const RtlirGenBlockSubroutine& sub) { return sub.decl == item; });
}

int NamedVariableKind(const DataType& type, const SubroutineScope& where,
                      const RtlirDesign& design) {
  if (where.mod != nullptr && type.scope_name.empty()) {
    return VpiNamedTypeVariableKind(design, *where.mod, type.type_name);
  }
  return VpiScopedTypeVariableKind(
      design, where.package != nullptr ? where.package->name : "", type);
}

int DeclaredVariableKind(const DataType& type, bool unpacked,
                         const SubroutineScope& where,
                         const RtlirDesign& design) {
  const int kKind = type.kind == DataTypeKind::kNamed
                        ? NamedVariableKind(type, where, design)
                        : VpiDataTypeVariableKind(type.kind);
  if (!unpacked) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiArrayVar;
}

VpiObject* MakeVariable(VpiObject* tf, std::string_view name, int kind,
                        bool automatic, const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = kind;
  var->name = build.keep(std::string(name));
  var->full_name = tf->full_name + "." + std::string(name);
  var->parent = tf;
  var->automatic = automatic;
  var->alloc_scheme = VpiAllocSchemeFor(automatic ? VpiAllocKind::kFrameOrThread
                                                  : VpiAllocKind::kOther);
  tf->children.push_back(var);
  return var;
}

int ArgumentDirection(Direction direction) {
  switch (direction) {
    case Direction::kOutput:
      return vpiOutput;
    case Direction::kInout:
      return vpiInout;
    case Direction::kRef:
      return vpiRef;
    default:
      return vpiInput;
  }
}

void MakeIoDecls(VpiObject* tf, const ModuleItem& item,
                 const SubroutineScope& where, const SubroutineBuild& sb) {
  for (const FunctionArg& arg : item.func_args) {
    VpiObject* var = MakeVariable(
        tf, arg.name,
        DeclaredVariableKind(arg.data_type, !arg.unpacked_dims.empty(), where,
                             sb.design),
        tf->automatic, sb.build);
    var->decl_facts.two_state = !DeclaredTypeIs4State(arg.data_type, sb.ctx);
    var->decl_facts.vif_interface =
        VpiVirtualInterfaceOf(sb.design, &arg.data_type, where.mod);
    AttachDeclaredRanges(var, arg.data_type, arg.unpacked_dims, sb.ctx,
                         sb.build);
    VpiRecordDeclaredShape(var, arg.data_type);
    if (arg.unpacked_dims.empty()) {
      var->size = static_cast<int>(DeclaredTypeWidth(arg.data_type, sb.ctx));
    }
    VpiObject* io_decl = sb.build.alloc();
    io_decl->type = vpiIODecl;
    io_decl->name = var->name;
    io_decl->full_name = var->full_name;
    io_decl->parent = tf;
    io_decl->direction =
        VpiIoDeclDirection(ArgumentDirection(arg.direction), false, false,
                           var->type == vpiVirtualInterfaceVar);
    io_decl->io_expr = var;
    if (arg.direction == Direction::kRef) {
      VpiObject* ref_obj = sb.build.alloc();
      ref_obj->type = vpiRefObj;
      ref_obj->parent = io_decl;
      ref_obj->name = io_decl->name;
      ref_obj->full_name = io_decl->full_name;
      ref_obj->actual = var;
      io_decl->io_expr = ref_obj;
    }
    tf->children.push_back(io_decl);
  }
}

int FuncTypeOf(const DataType& type) {
  switch (type.kind) {
    case DataTypeKind::kInteger:
      return vpiIntFunc;
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return vpiRealFunc;
    case DataTypeKind::kTime:
      return vpiTimeFunc;
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return type.is_signed ? vpiSizedSignedFunc : vpiSizedFunc;
    default:
      return vpiOtherFunc;
  }
}

void MakeReturnVariable(VpiObject* tf, const ModuleItem& item,
                        const SubroutineScope& where,
                        const SubroutineBuild& sb) {
  const DataType& type = item.return_type;
  if (IsTask(item) || type.kind == DataTypeKind::kVoid) return;
  VpiObject* ret = sb.build.alloc();
  ret->type = DeclaredVariableKind(type, !item.return_array_dims.empty(), where,
                                   sb.design);
  ret->name = tf->name;
  ret->full_name = tf->full_name;
  ret->parent = tf;
  ret->automatic = tf->automatic;
  ret->alloc_scheme = VpiAllocSchemeFor(
      tf->automatic ? VpiAllocKind::kFrameOrThread : VpiAllocKind::kOther);
  ret->decl_signed = type.is_signed;
  AttachDeclaredRanges(ret, type, item.return_array_dims, sb.ctx, sb.build);
  if (item.return_array_dims.empty()) {
    ret->size = static_cast<int>(DeclaredTypeWidth(type, sb.ctx));
  }
  const PackedDims kDims = WrittenPackedDims(&type, sb.ctx);
  if (!kDims.empty()) {
    tf->left_range = VpiIntConstant(kDims.front().left, sb.build);
    tf->right_range = VpiIntConstant(kDims.front().right, sb.build);
  }
  tf->return_var = ret;
  tf->func_type = FuncTypeOf(type);
  tf->decl_signed = type.is_signed;
  tf->size = VpiFunctionSize(false, ret->size != 0, ret->size);
}

void MakeBodyVariables(VpiObject* tf, const ModuleItem& item,
                       const SubroutineScope& where,
                       const SubroutineBuild& sb) {
  for (const Stmt* stmt : item.func_body_stmts) {
    if (stmt->kind != StmtKind::kVarDecl || stmt->var_is_param) continue;
    const bool kAutomatic =
        stmt->var_is_automatic || (tf->automatic && !stmt->var_is_static);
    VpiObject* var =
        MakeVariable(tf, stmt->var_name,
                     DeclaredVariableKind(stmt->var_decl_type,
                                          !stmt->var_unpacked_dims.empty(),
                                          where, sb.design),
                     kAutomatic, sb.build);
    var->decl_facts.two_state =
        !DeclaredTypeIs4State(stmt->var_decl_type, sb.ctx);
    var->decl_facts.vif_interface =
        VpiVirtualInterfaceOf(sb.design, &stmt->var_decl_type, where.mod);
    AttachDeclaredRanges(var, stmt->var_decl_type, stmt->var_unpacked_dims,
                         sb.ctx, sb.build);
  }
}

VpiObject* MakeSubroutine(const SubroutineScope& where, const ModuleItem* item,
                          const SubroutineBuild& sb) {
  VpiObject* tf = sb.build.alloc();
  tf->type = IsTask(*item) ? vpiTask : vpiFunction;
  tf->name = sb.build.keep(std::string(item->name));
  tf->full_name = VpiScopedFullName(where.scope, item->name);
  tf->parent = where.scope;
  tf->automatic = item->is_automatic || (where.automatic && !item->is_static);
  if (item->kind == ModuleItemKind::kDpiImport) MarkDpi(tf, *item);
  where.scope->children.push_back(tf);
  sb.made[{item, where.key}] = tf;
  VpiRecordWrittenLocation(tf, item->loc, sb.ctx);
  VpiAttachAttributes(tf, VpiNodeAttributes(where.mod, item), false, sb.ctx,
                      sb.build);
  InstancePrefixOverride scope(sb.ctx.InstancePrefixOverride(), where.params);
  MakeIoDecls(tf, *item, where, sb);
  MakeReturnVariable(tf, *item, where, sb);
  MakeBodyVariables(tf, *item, where, sb);
  return tf;
}

void MakeScopeSubroutines(const SubroutineBuild& sb, const RtlirModule& mod,
                          VpiObject* scope, const std::string& prefix) {
  const bool kAutomatic = mod.is_automatic;
  const std::string kParams = prefix.empty() ? "" : prefix + ".";
  for (const ModuleItem* item : mod.function_decls) {
    if (DeclaredInGenerateBlock(mod, item) || DefinesClassMethod(mod, item)) {
      continue;
    }
    MakeSubroutine({scope, prefix, kAutomatic, &mod, kParams}, item, sb);
  }
  for (const RtlirGenBlockSubroutine& sub : mod.gen_block_subroutines) {
    VpiObject* block = VpiGenScopeOf(scope, sub.gen_block_path);
    MakeSubroutine({block, block->full_name, kAutomatic, &mod, kParams},
                   sub.decl, sb);
  }
  for (const ModuleItem* item : mod.dpi_import_decls) {
    MakeSubroutine({scope, prefix, kAutomatic, &mod, kParams}, item, sb);
  }
  MarkDpiExports(scope, mod.dpi_export_decls);
}

void MakeInstanceSubroutines(const SubroutineBuild& sb,
                             const VpiObjectMap& objects) {
  WalkInstancePaths(
      &sb.design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        MakeScopeSubroutines(sb, *mod, scope, prefix);
      });
}

void MakePackageSubroutines(const SubroutineBuild& sb,
                            const VpiObjectMap& objects) {
  for (const PackageDecl* pkg : sb.design.packages) {
    const std::string kPackage(pkg->name);
    const SubroutineScope kWhere{FindObjectForFlatName(objects, kPackage),
                                 kPackage,
                                 pkg->is_automatic,
                                 nullptr,
                                 "",
                                 pkg};
    for (const ModuleItem* item : pkg->items) {
      if (IsSubroutine(item) && item->method_class.empty()) {
        MakeSubroutine(kWhere, item, sb);
      }
    }
    MarkDpiExports(kWhere.scope, pkg->items);
  }
}

void MakeUnitSubroutines(const SubroutineBuild& sb,
                         const VpiObjectMap& objects) {
  for (const VpiUnitScope& at : VpiUnitScopes(sb.design, objects)) {
    const SubroutineScope kWhere{at.scope, "$unit", false, nullptr, ""};
    for (const ModuleItem* item : at.unit->cu_items) {
      if (IsSubroutine(item) && item->method_class.empty()) {
        MakeSubroutine(kWhere, item, sb)->in_compilation_unit = true;
      }
    }
    MarkDpiExports(at.scope, at.unit->cu_items);
  }
}

const ModuleItem* SubroutineNamed(const std::vector<ModuleItem*>& decls,
                                  std::string_view name) {
  for (const ModuleItem* decl : decls) {
    if (IsSubroutine(decl) && decl->name == name) return decl;
  }
  return nullptr;
}

const ModuleItem* DpiImportNamed(const RtlirModule& mod,
                                 std::string_view name) {
  for (const ModuleItem* item : mod.dpi_import_decls) {
    if (item->name == name) return item;
  }
  return nullptr;
}

const ModuleItem* UnitSubroutineNamed(const RtlirDesign& design,
                                      const RtlirModule& mod,
                                      std::string_view name) {
  const CompilationUnit* unit =
      mod.unit_index >= 0
          ? design.compilation_units[static_cast<std::size_t>(mod.unit_index)]
          : design.compilation_unit;
  return unit == nullptr ? nullptr : SubroutineNamed(unit->cu_items, name);
}

VpiCalledSubroutine Called(const ModuleItem* decl, const std::string& key,
                           const VpiSubroutineObjects& made) {
  auto found = made.find({decl, key});
  return {decl, found == made.end() ? nullptr : found->second};
}

VpiCalledSubroutine GenerateBlockSubroutine(const VpiCallSite& site,
                                            std::string_view name) {
  for (const VpiObject* scope = site.scope; scope != nullptr;
       scope = scope->parent) {
    for (const RtlirGenBlockSubroutine& sub : site.mod.gen_block_subroutines) {
      if (sub.decl->name != name) continue;
      auto found = site.made.find({sub.decl, scope->full_name});
      if (found != site.made.end()) return {sub.decl, found->second};
    }
  }
  return {};
}

const ModuleItem* InstanceSubroutine(const RtlirModule& mod,
                                     std::string_view name) {
  for (const ModuleItem* decl : mod.function_decls) {
    if (decl->name == name && !DeclaredInGenerateBlock(mod, decl)) {
      return decl;
    }
  }
  return nullptr;
}

const ModuleDecl* EnclosingDecl(const CompilationUnit& unit,
                                const ModuleDecl* decl) {
  std::vector<const ModuleDecl*> work;
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    work.insert(work.end(), list->begin(), list->end());
  }
  while (!work.empty()) {
    const ModuleDecl* at = work.back();
    work.pop_back();
    for (const ModuleItem* item : at->items) {
      if (item->kind != ModuleItemKind::kNestedModuleDecl) continue;
      if (item->nested_module_decl == decl) return at;
      work.push_back(item->nested_module_decl);
    }
  }
  return nullptr;
}

}  // namespace

const ModuleDecl& VpiElementDeclFrom(const ModuleDecl* holder,
                                     const CompilationUnit& unit,
                                     std::string_view name) {
  for (const ModuleDecl* at = holder; at != nullptr;
       at = EnclosingDecl(unit, at)) {
    for (const ModuleItem* item : at->items) {
      if (item->kind == ModuleItemKind::kNestedModuleDecl &&
          item->nested_module_decl->name == name) {
        return *item->nested_module_decl;
      }
    }
  }
  static const ModuleDecl kNone;
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl->name == name) return *decl;
    }
  }
  return kNone;
}

const ModuleDecl& VpiDeclOf(const RtlirModule& mod) {
  static const ModuleDecl kNone;
  return mod.decl == nullptr ? kNone : *mod.decl;
}

VpiSubroutineObjects AttachSubroutines(const RtlirDesign& design,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build) {
  VpiSubroutineObjects made;
  const SubroutineBuild kBuild{design, ctx, build, made};
  MakeInstanceSubroutines(kBuild, objects);
  MakePackageSubroutines(kBuild, objects);
  MakeUnitSubroutines(kBuild, objects);
  return made;
}

void VpiMakeMethodContents(VpiObject* method, const ModuleItem& item,
                           const VpiMethodScope& where, SimContext& ctx,
                           const VpiAttachBuild& build) {
  const PackageDecl* package = nullptr;
  for (const PackageDecl* decl : where.design.packages) {
    if (decl->name == where.package) package = decl;
  }
  VpiSubroutineObjects unfiled;
  const SubroutineBuild kBuild{where.design, ctx, build, unfiled};
  const SubroutineScope kWhere{method->parent, "",           true,
                               where.mod,      where.params, package};
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), where.params);
  MakeIoDecls(method, item, kWhere, kBuild);
  MakeReturnVariable(method, item, kWhere, kBuild);
  MakeBodyVariables(
      method,
      item.out_of_block_body != nullptr ? *item.out_of_block_body : item,
      kWhere, kBuild);
}

VpiCalledSubroutine VpiPackageSubroutine(const RtlirDesign& design,
                                         std::string_view package,
                                         std::string_view name,
                                         const VpiSubroutineObjects& made) {
  for (const PackageDecl* decl : design.packages) {
    if (decl->name != package) continue;
    const ModuleItem* found = SubroutineNamed(decl->items, name);
    if (found != nullptr) return Called(found, std::string(package), made);
  }
  return {};
}

namespace {

const RtlirModule* ModuleAtPrefix(const RtlirDesign& design,
                                  std::string_view prefix) {
  if (design.top_modules.empty()) return nullptr;
  const RtlirModule* mod = design.top_modules.front();
  for (std::size_t start = 0; mod != nullptr && start < prefix.size();) {
    std::size_t end = prefix.find('.', start);
    if (end == std::string_view::npos) end = prefix.size();
    const std::string_view kName = prefix.substr(start, end - start);
    const RtlirModule* next = nullptr;
    for (const RtlirModuleInst& child : mod->children) {
      if (child.inst_name == kName) next = child.resolved;
    }
    mod = next;
    start = end + 1;
  }
  return mod;
}

VpiCalledSubroutine EnclosingSubroutine(const VpiCallSite& site,
                                        std::string_view name) {
  std::string prefix = site.prefix;
  while (!prefix.empty()) {
    const std::size_t kDot = prefix.rfind('.');
    prefix.resize(kDot == std::string::npos ? 0 : kDot);
    const RtlirModule* mod = ModuleAtPrefix(site.design, prefix);
    const ModuleItem* found =
        mod == nullptr ? nullptr : InstanceSubroutine(*mod, name);
    if (found != nullptr) return Called(found, prefix, site.made);
  }
  return {};
}

std::vector<std::string_view> PackagesSearched(const RtlirDesign& design,
                                               std::string_view package,
                                               std::string_view name) {
  std::vector<std::string_view> searched{package};
  for (const PackageDecl* decl : design.packages) {
    if (decl->name != package) continue;
    for (const ModuleItem* item : decl->items) {
      if (item->kind != ModuleItemKind::kImportDecl) continue;
      const ImportItem& imported = item->import_item;
      if (imported.is_wildcard || imported.item_name == name) {
        searched.push_back(imported.package_name);
      }
    }
  }
  return searched;
}

VpiCalledSubroutine PackageVisibleSubroutine(const VpiCallSite& site,
                                             std::string_view name) {
  VpiCalledSubroutine called;
  for (std::string_view package :
       PackagesSearched(site.design, site.package, name)) {
    if (called.decl == nullptr) {
      called = VpiPackageSubroutine(site.design, package, name, site.made);
    }
  }
  return called;
}

}  // namespace

VpiCalledSubroutine VpiNamedSubroutine(const VpiCallSite& site,
                                       std::string_view name) {
  if (!site.package.empty()) return PackageVisibleSubroutine(site, name);
  VpiCalledSubroutine called = GenerateBlockSubroutine(site, name);
  if (called.decl != nullptr) return called;
  if (const ModuleItem* found = InstanceSubroutine(site.mod, name)) {
    return Called(found, site.prefix, site.made);
  }
  if (const ModuleItem* found =
          UnitSubroutineNamed(site.design, site.mod, name)) {
    return Called(found, "$unit", site.made);
  }
  for (const RtlirImport& entry : site.mod.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    called =
        VpiPackageSubroutine(site.design, entry.package_name, name, site.made);
    if (called.decl != nullptr) return called;
  }
  if (const ModuleItem* found = DpiImportNamed(site.mod, name)) {
    return Called(found, site.prefix, site.made);
  }
  if (const ModuleItem* local =
          SubroutineNamed(site.mod.function_decls, name)) {
    return {local, nullptr};
  }
  return EnclosingSubroutine(site, name);
}

VpiCalledSubroutine VpiCalleeSubroutine(const VpiCallSite& site,
                                        const Expr& callee) {
  if (callee.kind == ExprKind::kIdentifier) {
    return VpiNamedSubroutine(site, callee.text);
  }
  if (!VpiIsPackageScopedName(callee)) return {};
  return VpiPackageSubroutine(site.design, callee.lhs->text, callee.rhs->text,
                              site.made);
}

bool VpiIsPackageScopedName(const Expr& name) {
  return name.kind == ExprKind::kMemberAccess && name.is_scope_resolution &&
         name.lhs != nullptr && name.rhs != nullptr &&
         name.lhs->kind == ExprKind::kIdentifier &&
         name.rhs->kind == ExprKind::kIdentifier;
}

VpiCalleeResolver VpiCalleesAt(const VpiCallSite& site) {
  return [site](const Expr& callee) {
    return VpiCalleeSubroutine(site, callee).object;
  };
}

}  // namespace delta
