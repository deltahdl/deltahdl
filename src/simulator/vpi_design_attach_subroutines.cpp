#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Where the tasks and functions of one scope are made: the scope object
// holding them, null for the compilation unit where its data made none; the
// flat name the made objects are keyed under; whether the scope's default
// lifetime is automatic (§13.3.1, §13.4.2); the module of an instance, among
// whose declarations a named type resolves, null for a package or the
// compilation unit; the instance prefix a declared width's parameters are
// read under; and the package, among whose declarations a named type
// resolves, null for an instance or the compilation unit.
struct SubroutineScope {
  VpiObject* scope;
  std::string key;
  bool automatic;
  const RtlirModule* mod = nullptr;
  std::string params;
  const PackageDecl* package = nullptr;
};

// What every task and function is made with: the design, the run a declared
// width is evaluated in, the build, and the objects made so far.
struct SubroutineBuild {
  const RtlirDesign& design;
  SimContext& ctx;
  const VpiAttachBuild& build;
  VpiSubroutineObjects& made;
};

// The module, interface or program the compilation unit declares under
// `name`, null for none.
const ModuleDecl* ElementDeclNamed(const RtlirDesign& design,
                                   std::string_view name) {
  if (design.compilation_unit == nullptr) return nullptr;
  const CompilationUnit& unit = *design.compilation_unit;
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl->name == name) return decl;
    }
  }
  return nullptr;
}

bool IsSubroutine(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl;
}

// Whether `item` is a task or function one of `mod`'s generate blocks
// declares (§27.4), which the elaborator lists among the module's own too.
bool DeclaredInGenerateBlock(const RtlirModule& mod, const ModuleItem* item) {
  return std::ranges::any_of(
      mod.gen_block_subroutines,
      [item](const RtlirGenBlockSubroutine& sub) { return sub.decl == item; });
}

// §37.17 with §6.18: the object kind of a variable `where` declares with a
// type standing for `name`, resolved among the declarations of the instance's
// module, or of the package or the compilation unit (§26.3).
int NamedVariableKind(std::string_view name, const SubroutineScope& where,
                      const RtlirDesign& design) {
  if (where.mod != nullptr) {
    return VpiNamedTypeVariableKind(design, *where.mod, name);
  }
  return VpiPackageNamedTypeVariableKind(design, where.package, name);
}

// §37.17 with §37.27: the object kind of a variable `where` declares with
// `type`, an array var or a named event array where `unpacked`.
int DeclaredVariableKind(const DataType& type, bool unpacked,
                         const SubroutineScope& where,
                         const RtlirDesign& design) {
  const int kKind = type.kind == DataTypeKind::kNamed
                        ? NamedVariableKind(type.type_name, where, design)
                        : VpiDataTypeVariableKind(type.kind);
  if (!unpacked) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiArrayVar;
}

// §37.12: the variable `name` of `kind` the task or function `tf` declares,
// full-named under it, with its lifetime (§37.3.7).
VpiObject* MakeVariable(VpiObject* tf, std::string_view name, int kind,
                        bool automatic, const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = kind;
  var->name = build.keep(std::string(name));
  var->full_name = tf->full_name + "." + std::string(name);
  var->parent = tf;
  var->automatic = automatic;
  tf->children.push_back(var);
  return var;
}

// §37.13 detail 1: the vpiDirection of an argument declared `direction`. The
// parser gives an argument written without one the direction of the argument
// before it, and the first such argument an input (§13.3).
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

// §37.41 (figure): an io decl per argument `item` declares, in order, each
// reaching through vpiExpr (§37.13) the variable the argument declares in the
// task's or function's scope.
void MakeIoDecls(VpiObject* tf, const ModuleItem& item,
                 const SubroutineScope& where, const SubroutineBuild& sb) {
  for (const FunctionArg& arg : item.func_args) {
    VpiObject* var = MakeVariable(
        tf, arg.name,
        DeclaredVariableKind(arg.data_type, !arg.unpacked_dims.empty(), where,
                             sb.design),
        tf->automatic, sb.build);
    AttachDeclaredRanges(var, arg.data_type, arg.unpacked_dims, sb.ctx,
                         sb.build);
    VpiObject* io_decl = sb.build.alloc();
    io_decl->type = vpiIODecl;
    io_decl->name = var->name;
    io_decl->full_name = var->full_name;
    io_decl->parent = tf;
    io_decl->direction = ArgumentDirection(arg.direction);
    io_decl->io_expr = var;
    tf->children.push_back(io_decl);
  }
}

// §37.41 (figure): the vpiFuncType of a function returning `type`, the kind
// of value it returns. A type none of the Verilog kinds describes returns
// another type.
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

// §37.41 details 1 to 3 and 12: the variable a function holds its return
// value in, of the function's own name and of the kind its return type
// takes, which vpiReturn reaches; the function's vpiFuncType; and its
// vpiSize, the variable's where the declaration determines it. A void
// function returns nothing and has size 0.
void MakeReturnVariable(VpiObject* tf, const ModuleItem& item,
                        const SubroutineScope& where,
                        const SubroutineBuild& sb) {
  const DataType& type = item.return_type;
  if (item.kind != ModuleItemKind::kFunctionDecl ||
      type.kind == DataTypeKind::kVoid) {
    return;
  }
  VpiObject* ret = sb.build.alloc();
  ret->type = DeclaredVariableKind(type, !item.return_array_dims.empty(), where,
                                   sb.design);
  ret->name = tf->name;
  ret->full_name = tf->full_name;
  ret->parent = tf;
  ret->automatic = tf->automatic;
  ret->decl_signed = type.is_signed;
  AttachDeclaredRanges(ret, type, item.return_array_dims, sb.ctx, sb.build);
  if (item.return_array_dims.empty()) {
    ret->size = static_cast<int>(DeclaredTypeWidth(type, sb.ctx));
  }
  // The figure's vpiLeftRange and vpiRightRange: the bounds of the leftmost
  // packed dimension the return type writes, none where it writes none.
  const PackedDims kDims = WrittenPackedDims(&type, sb.ctx);
  if (!kDims.empty()) {
    tf->left_range = VpiIntConstant(kDims.front().left, sb.build);
    tf->right_range = VpiIntConstant(kDims.front().right, sb.build);
  }
  tf->return_var = ret;
  tf->func_type = FuncTypeOf(type);
  tf->decl_signed = type.is_signed;
  tf->size =
      VpiFunctionSize(/*is_void_function=*/false, ret->size != 0, ret->size);
}

// §37.41 with §37.12: the variables the body of `item` declares, each
// automatic where it is declared so, or declared without a lifetime in an
// automatic task or function (§6.21).
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
    AttachDeclaredRanges(var, stmt->var_decl_type, stmt->var_unpacked_dims,
                         sb.ctx, sb.build);
  }
}

// §37.41 with §37.3.7, §13.3.1 and §13.4.2: the task or function `item`
// stands as in `where`, named after it, full-named under the scope (detail 5
// for a package's), automatic where it is declared so or declared without a
// lifetime in a scope whose default is automatic, and holding its io decls,
// its return variable and the variables its body declares. Answers the object
// made.
VpiObject* MakeSubroutine(const SubroutineScope& where, const ModuleItem* item,
                          const SubroutineBuild& sb) {
  VpiObject* tf = sb.build.alloc();
  tf->type = item->kind == ModuleItemKind::kTaskDecl ? vpiTask : vpiFunction;
  tf->name = sb.build.keep(std::string(item->name));
  tf->full_name = VpiScopedFullName(where.scope, item->name);
  tf->parent = where.scope;
  tf->automatic = item->is_automatic || (where.automatic && !item->is_static);
  if (where.scope != nullptr) where.scope->children.push_back(tf);
  sb.made[{item, where.key}] = tf;
  // A declared width or range reads the parameters of the scope declaring it.
  InstancePrefixOverride scope(sb.ctx.InstancePrefixOverride(), where.params);
  MakeIoDecls(tf, *item, where, sb);
  MakeReturnVariable(tf, *item, where, sb);
  MakeBodyVariables(tf, *item, where, sb);
  return tf;
}

// The tasks and functions the instance `scope` of `mod`, keyed under
// `prefix`, declares, those of its generate blocks under the block instance
// declaring them (§27.4), keyed under that block's full name.
void MakeScopeSubroutines(const SubroutineBuild& sb, const RtlirModule& mod,
                          VpiObject* scope, const std::string& prefix) {
  const ModuleDecl* decl = ElementDeclNamed(sb.design, mod.name);
  const bool kAutomatic = decl != nullptr && decl->is_automatic;
  const std::string kParams = prefix.empty() ? "" : prefix + ".";
  for (const ModuleItem* item : mod.function_decls) {
    if (DeclaredInGenerateBlock(mod, item)) continue;
    MakeSubroutine({scope, prefix, kAutomatic, &mod, kParams}, item, sb);
  }
  for (const RtlirGenBlockSubroutine& sub : mod.gen_block_subroutines) {
    VpiObject* block = VpiGenScopeOf(scope, sub.gen_block_path);
    if (block == nullptr) continue;
    MakeSubroutine({block, block->full_name, kAutomatic, &mod, kParams},
                   sub.decl, sb);
  }
}

// The tasks and functions each module instance declares.
void MakeInstanceSubroutines(const SubroutineBuild& sb,
                             const VpiObjectMap& objects) {
  WalkInstancePaths(
      &sb.design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        MakeScopeSubroutines(sb, *mod, scope, prefix);
      });
}

// The tasks and functions each package declares, among its other items.
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
      if (IsSubroutine(item)) MakeSubroutine(kWhere, item, sb);
    }
  }
}

// The tasks and functions of the compilation unit, which the unit's scope
// object holds where its data made one. §37.10 detail 6: none is reached by
// name.
void MakeUnitSubroutines(const SubroutineBuild& sb,
                         const VpiObjectMap& objects) {
  auto unit = objects.find("$unit");
  const SubroutineScope kWhere{unit == objects.end() ? nullptr : unit->second,
                               "$unit", false, nullptr, ""};
  for (const ModuleItem* item : sb.design.cu_function_decls) {
    MakeSubroutine(kWhere, item, sb)->in_compilation_unit = true;
  }
}

// The task or function `decls` declare under `name`, null where they declare
// none.
const ModuleItem* SubroutineNamed(const std::vector<ModuleItem*>& decls,
                                  std::string_view name) {
  for (const ModuleItem* decl : decls) {
    if (IsSubroutine(decl) && decl->name == name) return decl;
  }
  return nullptr;
}

// `decl` with the object made for it in the scope keyed `key`, null where
// none was made there.
VpiCalledSubroutine Called(const ModuleItem* decl, const std::string& key,
                           const VpiSubroutineObjects& made) {
  auto found = made.find({decl, key});
  return {decl, found == made.end() ? nullptr : found->second};
}

// §27.4: the task or function `name` of a generate block enclosing `site`,
// the innermost block declaring one first, null where none does.
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

// The task or function `name` the instance's module declares outside every
// generate block, null where it declares none. The module's function_decls
// hold its tasks and functions alone.
const ModuleItem* InstanceSubroutine(const RtlirModule& mod,
                                     std::string_view name) {
  for (const ModuleItem* decl : mod.function_decls) {
    if (decl->name == name && !DeclaredInGenerateBlock(mod, decl)) {
      return decl;
    }
  }
  return nullptr;
}

}  // namespace

VpiSubroutineObjects AttachSubroutines(const RtlirDesign& design,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build) {
  // §37.41: each task and function a design declares is a task or function
  // object of the instance, generate block or package declaring it. Nothing
  // made one, so vpiTaskFunc reached none and no call reached what it calls.
  VpiSubroutineObjects made;
  const SubroutineBuild kBuild{design, ctx, build, made};
  MakeInstanceSubroutines(kBuild, objects);
  MakePackageSubroutines(kBuild, objects);
  MakeUnitSubroutines(kBuild, objects);
  return made;
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

VpiCalledSubroutine VpiNamedSubroutine(const VpiCallSite& site,
                                       std::string_view name) {
  VpiCalledSubroutine called = GenerateBlockSubroutine(site, name);
  if (called.decl != nullptr) return called;
  if (const ModuleItem* found = InstanceSubroutine(site.mod, name)) {
    return Called(found, site.prefix, site.made);
  }
  if (const ModuleItem* found =
          SubroutineNamed(site.design.cu_function_decls, name)) {
    return Called(found, "$unit", site.made);
  }
  for (const RtlirImport& entry : site.mod.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    called =
        VpiPackageSubroutine(site.design, entry.package_name, name, site.made);
    if (called.decl != nullptr) return called;
  }
  // A generate block's task or function no block object holds, an unnamed
  // block's, still says what kind of call names it.
  return {SubroutineNamed(site.mod.function_decls, name), nullptr};
}

VpiCalledSubroutine VpiCalleeSubroutine(const VpiCallSite& site,
                                        const Expr& callee) {
  if (callee.kind == ExprKind::kIdentifier) {
    return VpiNamedSubroutine(site, callee.text);
  }
  const bool kPackageScoped = callee.kind == ExprKind::kMemberAccess &&
                              callee.is_scope_resolution &&
                              callee.lhs != nullptr && callee.rhs != nullptr &&
                              callee.lhs->kind == ExprKind::kIdentifier &&
                              callee.rhs->kind == ExprKind::kIdentifier;
  if (!kPackageScoped) return {};
  return VpiPackageSubroutine(site.design, callee.lhs->text, callee.rhs->text,
                              site.made);
}

VpiCalleeResolver VpiCalleesAt(const VpiCallSite& site) {
  return [site](const Expr& callee) {
    return VpiCalleeSubroutine(site, callee).object;
  };
}

}  // namespace delta
