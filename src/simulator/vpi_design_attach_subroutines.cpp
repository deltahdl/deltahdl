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
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_declared_shape.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_method_contents.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
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

// Whether `item` declares a task or function, or imports one through DPI
// (§35.5.4).
bool IsSubroutine(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kDpiImport;
}

// Whether the task or function `item` declares or imports is a task.
bool IsTask(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kTaskDecl || item.dpi_is_task;
}

// §37.41 details 6 to 10: marks `tf` as the task or function the DPI import
// or export declaration `decl` names, imported or exported, pure or context as
// an import declares it (§35.5.1.3), of the flavor its specification string
// names, and linking to the C name it writes or, where it writes none, to its
// own name (§35.5.4).
void MarkDpi(VpiObject* tf, const ModuleItem& decl) {
  tf->is_dpi = true;
  tf->dpi_export = decl.kind == ModuleItemKind::kDpiExport;
  tf->dpi_pure = decl.dpi_is_pure;
  tf->dpi_context = decl.dpi_is_context;
  tf->is_dpi_c = decl.dpi_spec_string == "DPI-C";
  tf->dpi_c_identifier =
      std::string(decl.dpi_c_name.empty() ? decl.name : decl.dpi_c_name);
}

// §35.7: marks as exported each task or function of `scope` that an export
// declaration among `items` names, an export naming one its own scope
// declares.
void MarkDpiExports(VpiObject* scope, const std::vector<ModuleItem*>& items) {
  if (scope == nullptr) return;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kDpiExport) continue;
    for (VpiObject* child : scope->children) {
      const bool kTaskFunc =
          child->type == vpiTask || child->type == vpiFunction;
      if (kTaskFunc && child->name == item->name) MarkDpi(child, *item);
    }
  }
}

// §8.24: whether `item` is the body of a method written outside its class,
// `C::name`, for a class `mod` declares. It defines a method of the class
// (§37.31 detail 1) and declares no task or function of the module. A body a
// module writes for a task of an interface port, `a.name` (§25.7.3), is the
// module's own.
bool DefinesClassMethod(const RtlirModule& mod, const ModuleItem* item) {
  return std::ranges::any_of(mod.class_decls, [item](const ClassDecl* decl) {
    return decl->name == item->method_class;
  });
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
  // §37.3.7: an automatic variable is allocated with the frame of its call.
  var->alloc_scheme = VpiAllocSchemeFor(automatic ? VpiAllocKind::kFrameOrThread
                                                  : VpiAllocKind::kOther);
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
    var->decl_facts.vif_interface =
        VpiVirtualInterfaceOf(sb.design, &arg.data_type);
    AttachDeclaredRanges(var, arg.data_type, arg.unpacked_dims, sb.ctx,
                         sb.build);
    // §37.13: the io decl reports the size, signing and shape of the variable
    // it declares, which no RtlirVariable records for an argument.
    VpiRecordDeclaredShape(var, arg.data_type);
    if (arg.unpacked_dims.empty()) {
      var->size = static_cast<int>(DeclaredTypeWidth(arg.data_type, sb.ctx));
    }
    VpiObject* io_decl = sb.build.alloc();
    io_decl->type = vpiIODecl;
    io_decl->name = var->name;
    io_decl->full_name = var->full_name;
    io_decl->parent = tf;
    // §37.13 details 1 and 3: vpiRef for an argument passed by reference, its
    // vpiExpr a ref obj whose actual is the variable (detail 2), and no
    // direction for a virtual interface (§25.9).
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
    var->decl_facts.vif_interface =
        VpiVirtualInterfaceOf(sb.design, &stmt->var_decl_type);
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
  tf->type = IsTask(*item) ? vpiTask : vpiFunction;
  tf->name = sb.build.keep(std::string(item->name));
  tf->full_name = VpiScopedFullName(where.scope, item->name);
  tf->parent = where.scope;
  tf->automatic = item->is_automatic || (where.automatic && !item->is_static);
  if (item->kind == ModuleItemKind::kDpiImport) MarkDpi(tf, *item);
  if (where.scope != nullptr) where.scope->children.push_back(tf);
  sb.made[{item, where.key}] = tf;
  // §37.3.3: where the task or function was written.
  VpiRecordWrittenLocation(tf, item->loc, sb.ctx);
  // §37.83: the attributes it is written with.
  VpiAttachAttributes(tf, VpiNodeAttributes(where.mod, item), false, sb.ctx,
                      sb.build);
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
  const bool kAutomatic = ElementDeclNamed(sb.design, mod.name).is_automatic;
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
      // §8.24: a package names no interface port, so a body written `C::name`
      // in it is a method of its class C.
      if (IsSubroutine(item) && item->method_class.empty()) {
        MakeSubroutine(kWhere, item, sb);
      }
    }
    MarkDpiExports(kWhere.scope, pkg->items);
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
    // §8.24: as in a package, a body written `C::name` is a method of C.
    if (!item->method_class.empty()) continue;
    MakeSubroutine(kWhere, item, sb)->in_compilation_unit = true;
  }
  if (sb.design.compilation_unit == nullptr) return;
  // §35.5.4: what the unit imports through DPI, which its list of functions
  // leaves out.
  const std::vector<ModuleItem*>& items = sb.design.compilation_unit->cu_items;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      MakeSubroutine(kWhere, item, sb)->in_compilation_unit = true;
    }
  }
  MarkDpiExports(kWhere.scope, items);
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

// §35.5: the task or function `mod` imports through DPI under `name`, null
// for none.
const ModuleItem* DpiImportNamed(const RtlirModule& mod,
                                 std::string_view name) {
  for (const ModuleItem* item : mod.dpi_import_decls) {
    if (item->name == name) return item;
  }
  return nullptr;
}

// §35.5.4: the task or function the compilation unit of `design` imports
// through DPI under `name`, null for none.
const ModuleItem* UnitDpiImportNamed(const RtlirDesign& design,
                                     std::string_view name) {
  if (design.compilation_unit == nullptr) return nullptr;
  for (const ModuleItem* item : design.compilation_unit->cu_items) {
    if (item->kind == ModuleItemKind::kDpiImport && item->name == name) {
      return item;
    }
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

const ModuleDecl& ElementDeclNamed(const RtlirDesign& design,
                                   std::string_view name) {
  static const ModuleDecl kNone;
  if (design.compilation_unit == nullptr) return kNone;
  const CompilationUnit& unit = *design.compilation_unit;
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl->name == name) return *decl;
    }
  }
  return kNone;
}

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

void VpiMakeMethodContents(VpiObject* method, const ModuleItem& item,
                           const VpiMethodScope& where, SimContext& ctx,
                           const VpiAttachBuild& build) {
  const PackageDecl* package = nullptr;
  for (const PackageDecl* decl : where.design.packages) {
    if (decl->name == where.package) package = decl;
  }
  // A method is reached through its class defn, so nothing files it among the
  // tasks and functions a call finds by declaration.
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

// The module of the instance whose objects are keyed under `prefix`, reached
// from the first top through the child each component names; null where a
// component names no child, as a generate block's does.
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

// §23.8: the task or function `name` the module of an instance enclosing the
// call's declares, the nearest first, up to the root of the hierarchy, with
// the object made for it there; none where no enclosing module declares one.
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

// §26.2 with §26.3: the packages a call of `name` standing in the package
// `package` finds its callee among, in the order it looks: the package
// itself, then the one each import it writes names, a named import of `name`
// or a wildcard one, in the order written. A package refers to none of the
// compilation unit's declarations (§26.2).
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

// The task or function `name` a call standing in a package reaches: the
// first PackagesSearched names declares.
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
          SubroutineNamed(site.design.cu_function_decls, name)) {
    return Called(found, "$unit", site.made);
  }
  if (const ModuleItem* found = UnitDpiImportNamed(site.design, name)) {
    return Called(found, "$unit", site.made);
  }
  for (const RtlirImport& entry : site.mod.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    called =
        VpiPackageSubroutine(site.design, entry.package_name, name, site.made);
    if (called.decl != nullptr) return called;
  }
  // §35.5.4: a task or function the module imports through DPI.
  if (const ModuleItem* found = DpiImportNamed(site.mod, name)) {
    return Called(found, site.prefix, site.made);
  }
  // A generate block's task or function written where no block enclosing the
  // call declares it still says what kind of call names it, though no task or
  // function object stands for it there.
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
