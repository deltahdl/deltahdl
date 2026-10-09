#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §6.11, §6.12 and §6.17: the data type a type keyword names alone.
struct KeywordType {
  TokenKind keyword;
  DataTypeKind type;
};
constexpr KeywordType kKeywordTypes[] = {
    {TokenKind::kKwLogic, DataTypeKind::kLogic},
    {TokenKind::kKwReg, DataTypeKind::kReg},
    {TokenKind::kKwBit, DataTypeKind::kBit},
    {TokenKind::kKwByte, DataTypeKind::kByte},
    {TokenKind::kKwShortint, DataTypeKind::kShortint},
    {TokenKind::kKwInt, DataTypeKind::kInt},
    {TokenKind::kKwLongint, DataTypeKind::kLongint},
    {TokenKind::kKwInteger, DataTypeKind::kInteger},
    {TokenKind::kKwTime, DataTypeKind::kTime},
    {TokenKind::kKwReal, DataTypeKind::kReal},
    {TokenKind::kKwShortreal, DataTypeKind::kShortreal},
    {TokenKind::kKwRealtime, DataTypeKind::kRealtime},
    {TokenKind::kKwString, DataTypeKind::kString},
    {TokenKind::kKwEvent, DataTypeKind::kEvent},
};

// The data type `keyword` names alone; kImplicit where it names none.
DataTypeKind KeywordDataType(TokenKind keyword) {
  for (const KeywordType& entry : kKeywordTypes) {
    if (entry.keyword == keyword) return entry.type;
  }
  return DataTypeKind::kImplicit;
}

// §37.51 detail 3 with §37.25: the kind of typespec a property formal declared
// with the type keyword `keyword` reaches, 0 for an untyped formal, which
// reaches none. §16.12 adds sequence and property to the data types a formal
// may be declared with; §6.12 makes realtime a synonym for real.
int FormalTypespecKind(TokenKind keyword) {
  switch (keyword) {
    case TokenKind::kKwSequence:
      return vpiSequenceTypespec;
    case TokenKind::kKwProperty:
      return vpiPropertyTypespec;
    case TokenKind::kKwEvent:
      return vpiEventTypespec;
    case TokenKind::kKwRealtime:
      return vpiRealTypespec;
    default: {
      const DataTypeKind kType = KeywordDataType(keyword);
      return kType == DataTypeKind::kImplicit ? 0 : VpiTypespecKind(kType);
    }
  }
}

// §37.25: the typespec the typedef `name` declares in the scopes from
// `holder` out to the instance, or else among the compilation unit's, or else
// in a package an import of the module makes it visible from; null where none
// of them declares one.
VpiObject* TypedefTypespec(const VpiObject* holder, std::string_view name,
                           const VpiPropertyDeclSite& at) {
  for (const VpiObject* scope = holder; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    for (VpiObject* child : scope->children) {
      if (VpiIsTypespecType(child->type) && child->name == name) return child;
    }
  }
  auto it = at.unit_typespecs.find(name);
  return it != at.unit_typespecs.end()
             ? it->second
             : VpiImportedTypespec(name, at.imports, at.unit_typespecs);
}

// §37.25 with §37.31: a class typespec of the class `name`, hung from
// `formal`, reaching the class defn of that name a scope from the property out
// to the instance declares, where one does.
VpiObject* ClassTypespec(VpiObject* formal, std::string_view name,
                         const VpiAttachBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(name));
  typespec->parent = formal;
  for (const VpiObject* scope = formal->parent; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    for (VpiObject* child : scope->children) {
      if (child->type == vpiClassDefn && child->name == name) {
        typespec->children.push_back(child);
        return typespec;
      }
    }
  }
  return typespec;
}

// §37.51 detail 3 with §37.25: the typespec the formal `index` of `decl` is
// declared with, hung from `formal`: the one the typedef it names declares,
// which other objects of that type share (§37.17), a class typespec where it
// names a class (§16.8), or one of the type's own, reaching a range per
// packed dimension it was written with (§37.22); none for an untyped formal.
void MakeFormalTypespec(const ModuleItem& decl, size_t index, VpiObject* formal,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  const DataType* type = decl.prop_formal_types[index];
  if (type != nullptr && type->kind == DataTypeKind::kNamed) {
    VpiObject* named = TypedefTypespec(formal->parent, type->type_name, at);
    formal->children.push_back(
        named != nullptr ? named
                         : ClassTypespec(formal, type->type_name, build));
    return;
  }
  const TokenKind kKeyword = decl.prop_formal_type_kw[index];
  int kind = 0;
  if (kKeyword != TokenKind::kEof) {
    kind = FormalTypespecKind(kKeyword);
  } else if (type != nullptr) {
    kind = VpiTypespecKind(type->kind);
  }
  if (kind == 0) return;
  VpiObject* typespec = build.alloc();
  typespec->type = kind;
  typespec->parent = formal;
  formal->children.push_back(typespec);
  for (const PackedRange& dim : WrittenPackedDims(type, at.ctx)) {
    typespec->children.push_back(VpiRangeObject(typespec, dim, build));
  }
}

// §37.51: the prop formal decl the formal `index` of `decl` stands as, hung
// from `property`: named, of no direction unless it is a local variable
// argument (detail 5), reaching the typespec of the type it is declared with
// (detail 3) and the default value it declares, where it declares one,
// through vpiExpr (detail 4).
void MakePropFormal(const ModuleItem& decl, size_t index, VpiObject* property,
                    const VpiPropertyDeclSite& at, const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiPropFormalDecl;
  formal->parent = property;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction = VpiPropFormalDirection(decl.prop_formal_is_local[index]);
  MakeFormalTypespec(decl, index, formal, at, with.build);
  VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
  if (value != nullptr) formal->children.push_back(value);
  property->children.push_back(formal);
}

// §37.51 with §16.10: the variable the local variable `local` a property
// declares stands as, hung from the property decl `property` and named in
// it, of the kind its type is (§37.17). §37.52 detail 1 gives its value no
// access, so it holds none.
void MakePropertyVariable(const SeqLocalDecl& local, VpiObject* property,
                          const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = VpiDataTypeVariableKind(KeywordDataType(local.type_kw));
  var->parent = property;
  var->name = build.keep(std::string(local.name));
  var->full_name = VpiScopedFullName(property, local.name);
  property->children.push_back(var);
}

// The child of `scope` of `type` named `name`; null where none is.
VpiObject* ChildOfType(const VpiObject* scope, int type,
                       std::string_view name) {
  for (VpiObject* child : scope->children) {
    if (child->type == type && child->name == name) return child;
  }
  return nullptr;
}

// The scope among the children of `scope` that the prefix `prefix` of a
// property's name names: a clocking block, `cb.p` (§16.16 (b)), or an
// interface instance, `i0.p` (§16.12 with §23.6); null where it names
// neither.
VpiObject* PropertyHolderNamed(const VpiObject* scope,
                               std::string_view prefix) {
  VpiObject* block = ChildOfType(scope, vpiClockingBlock, prefix);
  return block != nullptr ? block : ChildOfType(scope, vpiInterface, prefix);
}

// §37.51: the property decl named `name` the scope standing around `holder`
// declares, the nearest from a generate block instance out to the instance;
// null where none was built. A name written through a clocking block or an
// interface instance is the property that block or instance declares.
VpiObject* PropertyDeclAround(const VpiObject* holder, std::string_view name) {
  const size_t kDot = name.find('.');
  for (VpiObject* scope = holder->parent; scope != nullptr;
       scope = scope->parent) {
    VpiObject* found = kDot == std::string_view::npos
                           ? ChildOfType(scope, vpiPropertyDecl, name)
                           : PropertyHolderNamed(scope, name.substr(0, kDot));
    if (found != nullptr && kDot != std::string_view::npos) {
      return ChildOfType(found, vpiPropertyDecl, name.substr(kDot + 1));
    }
    if (found != nullptr) return found;
    if (VpiIsInstanceType(scope->type)) break;
  }
  return nullptr;
}

// The typespec the formal `formal` was declared with, null for an untyped one.
const VpiObject* TypespecOf(const VpiObject* formal) {
  for (const VpiObject* child : formal->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

// §37.51 detail 2: the argument the actual `actual` of a property inst
// stands as, bound to a formal declared with the typespec `target`, null for
// an untyped one; null for an actual the instance leaves out. A sequence or
// property the actual writes (§16.12) is the property expr of the tree the
// parser carries it as (§37.52); §37.59 detail 4 makes the terminal `$`,
// which §16.8 admits as an actual, the unbounded constant; and a typed
// formal's typespec orders a keyed pattern (detail 6).
VpiObject* ActualArgument(const Expr* actual, const VpiObject* target,
                          const VpiStmtBuild& with) {
  if (actual == nullptr) return nullptr;
  if (actual->property_actual != nullptr) {
    return VpiPropertyExprObject(actual->property_actual, with, nullptr);
  }
  if (actual->text != "$") {
    return target != nullptr ? with.assigned(actual, target)
                             : with.expression(actual);
  }
  VpiObject* dollar = with.build.alloc();
  dollar->type = vpiConstant;
  dollar->const_type = vpiUnboundedConst;
  return dollar;
}

}  // namespace

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiPropertyInst;
  inst->parent = holder;
  const std::string_view kName =
      instance.kind == ExprKind::kCall ? instance.callee : instance.text;
  inst->property_decl = PropertyDeclAround(holder, kName);
  // §26.3: a property a package declares, which an import makes visible.
  if (inst->property_decl == nullptr) {
    inst->property_decl = with.imported_property(kName);
  }
  // §37.51 detail 2: an argument per formal, in the order declared, the
  // formal's default standing for an actual the instance leaves out; with no
  // declaration built, the actuals as written.
  const std::vector<VpiHandle> kFormals = VpiPropFormals(inst->property_decl);
  std::vector<const VpiObject*> targets(instance.args.size(), nullptr);
  for (std::size_t i = 0; i < std::min(targets.size(), kFormals.size()); ++i) {
    targets[i] = TypespecOf(kFormals[i]);
  }
  std::vector<VpiHandle> provided;
  provided.reserve(instance.args.size());
  for (std::size_t i = 0; i < instance.args.size(); ++i) {
    provided.push_back(ActualArgument(instance.args[i], targets[i], with));
  }
  std::vector<VpiPropertyFormal> formals;
  for (VpiHandle formal : kFormals) {
    formals.push_back(VpiPropertyFormal{VpiPropFormalInitExpr(formal)});
  }
  for (VpiHandle argument : formals.empty()
                                ? provided
                                : VpiPropertyInstArguments(formals, provided)) {
    if (argument != nullptr) inst->arguments.push_back(argument);
  }
  holder->children.push_back(inst);
  return inst;
}

VpiObject* VpiImportedPropertyDecl(std::string_view name,
                                   const std::vector<RtlirImport>& imports,
                                   const VpiObjectMap& objects) {
  for (const RtlirImport& imported : imports) {
    if (!imported.is_wildcard && imported.item_name != name) continue;
    VpiObject* decl =
        ChildOfType(FindObjectForFlatName(objects, imported.package_name),
                    vpiPropertyDecl, name);
    if (decl != nullptr) return decl;
  }
  return nullptr;
}

void AttachPackagePropertyDecls(const RtlirDesign& design,
                                const VpiObjectMap& objects,
                                const VpiObjectMap& unit_typespecs,
                                SimContext& ctx, const VpiAttachBuild& build) {
  // §16.12 with §37.10 detail 1: a property a package declares is a property
  // decl of the package, its expressions resolving among the package's names.
  const std::vector<RtlirImport> kNoImports;
  for (const PackageDecl* pkg : design.packages) {
    const std::string kPrefix(pkg->name);
    const VpiStmtBuild kWith{build,
                             [&](const Expr* expr) {
                               return VpiInstanceExpression(
                                   expr, objects, kPrefix, ctx, build);
                             },
                             nullptr,
                             nullptr,
                             nullptr,
                             nullptr};
    for (const ModuleItem* item : pkg->items) {
      if (item->kind != ModuleItemKind::kPropertyDecl) continue;
      VpiMakePropertyDecl(RtlirPropertyDecl{item, {}, {}, nullptr},
                          {FindObjectForFlatName(objects, pkg->name),
                           unit_typespecs, ctx, kNoImports},
                          kWith);
    }
  }
}

VpiObject* VpiMakePropertyDecl(const RtlirPropertyDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  VpiObject* scope = at.scope;
  // §37.12 with §14.3: a property a clocking block declares is of that block,
  // which AttachClockingBlocks has made under the same scope, the generate
  // block instance both are stamped with or the instance.
  if (declared.clocking_block != nullptr) {
    scope = ChildOfType(scope, vpiClockingBlock, declared.clocking_block->name);
  }
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = with.build.alloc();
  obj->type = vpiPropertyDecl;
  obj->parent = scope;
  // §16.16 (b): the run keys a clocking block's property under the block's
  // name and its own, `cb.p`, the block being its scope here.
  const std::string_view kName =
      declared.clocking_block == nullptr
          ? decl.name
          : decl.name.substr(decl.name.rfind('.') + 1);
  obj->name = with.build.keep(std::string(kName));
  obj->full_name = VpiScopedFullName(scope, kName);
  scope->children.push_back(obj);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    MakePropertyVariable(local, obj, with.build);
  }
  // §37.52: the body the parser read, its clock, its disable condition and,
  // for a Boolean property, its expression; a body of another shape was not
  // read and stands for no spec.
  const PropertyExprNode* tree = decl.prop_body_tree;
  if (tree == nullptr) return obj;
  VpiMakePropertySpecOf(
      obj, VpiPropertySpecParts{decl.prop_clock, decl.prop_disable_iff, tree},
      with);
  return obj;
}

}  // namespace delta
