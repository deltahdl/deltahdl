#include <algorithm>
#include <cstddef>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sequence_locals.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_vars.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_typespec_shapes.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

DataTypeKind KeywordDataType(TokenKind keyword) {
  return std::find_if(std::begin(kKeywordTypes), std::end(kKeywordTypes),
                      [keyword](const KeywordType& entry) {
                        return entry.keyword == keyword;
                      })
      ->type;
}

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
    default:
      return VpiTypespecKind(KeywordDataType(keyword));
  }
}

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

VpiObject* FormalPackedTypespec(const ModuleItem& decl, size_t index,
                                VpiObject* formal,
                                const VpiPropertyDeclSite& at,
                                const VpiAttachBuild& build) {
  const DataType* type = decl.prop_formal_types[index];
  if (type != nullptr && type->kind == DataTypeKind::kNamed) {
    const std::string kWritten = type->scope_name.empty()
                                     ? std::string(type->type_name)
                                     : std::string(type->scope_name) +
                                           "::" + std::string(type->type_name);
    VpiObject* named = TypedefTypespec(formal->parent, kWritten, at);
    return named != nullptr ? named
                            : ClassTypespec(formal, type->type_name, build);
  }
  const TokenKind kKeyword = decl.prop_formal_type_kw[index];
  int kind = 0;
  if (kKeyword != TokenKind::kEof && kKeyword != TokenKind::kKwUntyped) {
    kind = FormalTypespecKind(kKeyword);
  } else if (type != nullptr) {
    kind = VpiTypespecKind(type->kind);
  }
  if (kind == 0) return nullptr;
  VpiObject* typespec = build.alloc();
  typespec->type = kind;
  typespec->parent = formal;
  for (const PackedRange& dim : WrittenPackedDims(type, at.ctx)) {
    typespec->children.push_back(VpiRangeObject(typespec, dim, build));
  }
  return typespec;
}

VpiObject* FormalIndexTypespec(std::string_view written,
                               const VpiObject* formal,
                               const VpiPropertyDeclSite& at,
                               const VpiAttachBuild& build) {
  if (std::optional<DataTypeKind> kind = VpiAssocIndexKeywordKind(written)) {
    VpiObject* typespec = build.alloc();
    typespec->type = VpiTypespecKind(*kind);
    return typespec;
  }
  return TypedefTypespec(formal->parent, written, at);
}

void MakeFormalTypespec(const ModuleItem& decl, size_t index, VpiObject* formal,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  VpiObject* typespec = FormalPackedTypespec(decl, index, formal, at, build);
  if (typespec == nullptr) return;
  std::vector<VpiTypespecDim> dims;
  for (const Expr* dim : decl.prop_formal_unpacked_dims[index]) {
    VpiTypespecDim made = VpiUnpackedTypespecDim(dim, at.ctx);
    if (made.array_type == vpiAssocArray) {
      made.index_typespec = FormalIndexTypespec(dim->text, formal, at, build);
    }
    dims.push_back(made);
  }
  VpiTypespecShapes shapes(build);
  formal->children.push_back(shapes.Unnamed(formal, dims, typespec));
}

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

int SeqFormalDirection(const ModuleItem& decl, size_t index) {
  if (!decl.prop_formal_is_local[index]) return vpiNoDirection;
  const size_t kLocal = static_cast<size_t>(std::count(
      decl.prop_formal_is_local.begin(),
      decl.prop_formal_is_local.begin() + static_cast<std::ptrdiff_t>(index),
      true));
  switch (decl.prop_seq_local_lvar_directions[kLocal]) {
    case Direction::kOutput:
      return vpiOutput;
    case Direction::kInout:
      return vpiInout;
    default:
      return vpiInput;
  }
}

void MakeSeqFormal(const ModuleItem& decl, size_t index, VpiObject* sequence,
                   const VpiPropertyDeclSite& at, const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiSeqFormalDecl;
  formal->parent = sequence;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction = SeqFormalDirection(decl, index);
  MakeFormalTypespec(decl, index, formal, at, with.build);
  VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
  if (value != nullptr) formal->children.push_back(value);
  sequence->children.push_back(formal);
}

void MakeDeclaredVariable(const SeqLocalDecl& local, VpiObject* declared,
                          SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type =
      VpiDataTypeVariableKind(local.named_type.kind == DataTypeKind::kNamed
                                  ? DeclaredTypeKind(local.named_type, ctx)
                                  : KeywordDataType(local.type_kw));
  var->parent = declared;
  var->name = build.keep(std::string(local.name));
  var->full_name = VpiScopedFullName(declared, local.name);
  declared->children.push_back(var);
  VpiMakeVarBits(*var, LocalDataType(local),
                 LocalWidth(local, ctx, ctx.GetArena()), ctx, build);
  if (!local.packed_dims.empty()) return;
  if (const StructTypeInfo* layout = NamedLayout(local.named_type, ctx)) {
    VpiMakeLocalMembers(var, *layout, ctx, build);
  }
}

int FormalVariableKind(const DataType& type, const SimContext& ctx) {
  return VpiDataTypeVariableKind(type.kind == DataTypeKind::kNamed
                                     ? DeclaredTypeKind(type, ctx)
                                     : type.kind);
}

VpiObject* ChildOfType(const VpiObject* scope, int type,
                       std::string_view name) {
  for (VpiObject* child : scope->children) {
    if (child->type == type && child->name == name) return child;
  }
  return nullptr;
}

VpiObject* PropertyHolderNamed(const VpiObject* scope,
                               std::string_view prefix) {
  VpiObject* block = ChildOfType(scope, vpiClockingBlock, prefix);
  return block != nullptr ? block : ChildOfType(scope, vpiInterface, prefix);
}

VpiObject* DeclAround(const VpiObject* from, int type, std::string_view name) {
  const size_t kDot = name.find('.');
  for (const VpiObject* scope = from; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    VpiObject* found = kDot == std::string_view::npos
                           ? ChildOfType(scope, type, name)
                           : PropertyHolderNamed(scope, name.substr(0, kDot));
    if (found != nullptr && kDot != std::string_view::npos) {
      return ChildOfType(found, type, name.substr(kDot + 1));
    }
    if (found != nullptr) return found;
  }
  return nullptr;
}

const VpiObject* TypespecOf(const VpiObject* formal) {
  for (const VpiObject* child : formal->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

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

VpiObject* MakeDeclHead(const RtlirAssertionItemDecl& declared, int type,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  VpiObject* scope = at.scope;
  if (declared.clocking_block != nullptr) {
    scope = ChildOfType(scope, vpiClockingBlock, declared.clocking_block->name);
  }
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = build.alloc();
  obj->type = type;
  obj->parent = scope;
  const std::string_view kName =
      declared.clocking_block == nullptr
          ? decl.name
          : decl.name.substr(decl.name.rfind('.') + 1);
  obj->name = build.keep(std::string(kName));
  obj->full_name = VpiScopedFullName(scope, kName);
  scope->children.push_back(obj);
  return obj;
}

VpiObject* ImportedDecl(int type, std::string_view name,
                        const std::vector<RtlirImport>& imports,
                        const VpiObjectMap& objects) {
  VpiObject* found = nullptr;
  for (const RtlirImport& imported : imports) {
    if (found != nullptr ||
        (!imported.is_wildcard && imported.item_name != name)) {
      continue;
    }
    const VpiObject* pkg =
        FindObjectForFlatName(objects, imported.package_name);
    found = pkg != nullptr ? ChildOfType(pkg, type, name) : nullptr;
  }
  return found;
}

VpiObject* SequenceDeclBody(const ModuleItem& decl, const VpiStmtBuild& with) {
  VpiObject* body =
      VpiSequenceExprObject(decl.seq_linear, with, &decl.seq_clock);
  if (body == nullptr || decl.seq_clock.empty() ||
      body->type == vpiMulticlockSequenceExpr) {
    return body;
  }
  VpiObject* multiclock = with.build.alloc();
  multiclock->type = vpiMulticlockSequenceExpr;
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedSeq;
  clocked->parent = multiclock;
  clocked->clocking_event = VpiEventCondition(decl.seq_clock, with);
  clocked->children.push_back(body);
  multiclock->children.push_back(clocked);
  return multiclock;
}

VpiObject* MakeSequenceInst(VpiObject* decl, const Expr& instance,
                            const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiSequenceInst;
  inst->sequence_decl = decl;
  const std::vector<VpiHandle> kFormals = VpiSeqFormals(decl);
  std::vector<VpiHandle> provided;
  std::vector<VpiSequenceFormal> formals;
  formals.reserve(kFormals.size());
  for (std::size_t i = 0; i < kFormals.size(); ++i) {
    const Expr* actual = i < instance.args.size() ? instance.args[i] : nullptr;
    provided.push_back(ActualArgument(actual, TypespecOf(kFormals[i]), with));
    formals.push_back(VpiSequenceFormal{VpiSeqFormalInitExpr(kFormals[i])});
  }
  inst->arguments = VpiSequenceInstArguments(formals, provided);
  return inst;
}

VpiObject* NamedDecl(const Expr& operand, int type, const VpiStmtBuild& with) {
  switch (operand.kind) {
    case ExprKind::kIdentifier:
      return with.assertion_decl(type, {}, operand.text);
    case ExprKind::kCall:
      return operand.callee.empty()
                 ? NamedDecl(*operand.lhs, type, with)
                 : with.assertion_decl(type, {}, operand.callee);
    case ExprKind::kMemberAccess:
      return operand.is_scope_resolution
                 ? with.assertion_decl(type, operand.lhs->text,
                                       operand.rhs->text)
                 : nullptr;
    default:
      return nullptr;
  }
}

VpiObject* PropertyInstOf(VpiObject* decl, const Expr& instance,
                          const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiPropertyInst;
  inst->property_decl = decl;
  const std::vector<VpiHandle> kFormals = VpiPropFormals(decl);
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
  formals.reserve(kFormals.size());
  for (VpiHandle formal : kFormals) {
    formals.push_back(VpiPropertyFormal{VpiPropFormalInitExpr(formal)});
  }
  for (VpiHandle argument : formals.empty()
                                ? provided
                                : VpiPropertyInstArguments(formals, provided)) {
    if (argument != nullptr) inst->arguments.push_back(argument);
  }
  return inst;
}

}  // namespace

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const Expr* disable, const VpiStmtBuild& with) {
  VpiObject* inst = PropertyInstOf(NamedDecl(instance, vpiPropertyDecl, with),
                                   instance, with);
  inst->parent = holder;
  inst->disable_condition = with.expression(disable);
  holder->children.push_back(inst);
  return inst;
}

VpiObject* VpiPropertyOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with) {
  VpiObject* decl = NamedDecl(operand, vpiPropertyDecl, with);
  return decl != nullptr ? PropertyInstOf(decl, operand, with)
                         : VpiSequenceOperandObject(operand, with);
}

VpiObject* VpiAssertionDeclNamed(const VpiAssertionDeclName& named,
                                 const std::vector<RtlirImport>& imports,
                                 const VpiObjectMap& objects) {
  if (!named.package.empty()) {
    RtlirImport path;
    path.package_name = named.package;
    path.item_name = named.name;
    return ImportedDecl(named.type, named.name, {path}, objects);
  }
  VpiObject* declared = DeclAround(named.scope, named.type, named.name);
  return declared != nullptr
             ? declared
             : ImportedDecl(named.type, named.name, imports, objects);
}

VpiObject* VpiSequenceOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with) {
  VpiObject* decl = NamedDecl(operand, vpiSequenceDecl, with);
  return decl != nullptr ? MakeSequenceInst(decl, operand, with)
                         : with.expression(&operand);
}

void AttachPackageAssertionItemDecls(const RtlirDesign& design,
                                     const VpiObjectMap& objects,
                                     const VpiObjectMap& unit_typespecs,
                                     SimContext& ctx,
                                     const VpiAttachBuild& build) {
  const std::vector<RtlirImport> kNoImports;
  const std::vector<std::string_view> kNoGenBlocks;
  for (const PackageDecl* pkg : design.packages) {
    const std::string kPrefix(pkg->name);
    VpiObject* package = FindObjectForFlatName(objects, pkg->name);
    const VpiCallStand kStand{package, nullptr, pkg->name};
    const VpiExprNames kNames{
        objects, kPrefix, kNoGenBlocks, nullptr, &design.node_attrs, &kStand};
    const VpiStmtBuild kWith{
        build,
        [&](const Expr* expr) {
          return VpiGenBlockExpression(expr, kNames, ctx, build);
        },
        nullptr,
        nullptr,
        nullptr,
        [&](int type, std::string_view path, std::string_view name) {
          return VpiAssertionDeclNamed({package, type, path, name}, kNoImports,
                                       objects);
        }};
    const VpiPropertyDeclSite kAt{package, unit_typespecs, ctx, kNoImports};
    std::vector<std::pair<VpiObject*, const ModuleItem*>> made;
    for (const ModuleItem* item : pkg->items) {
      const RtlirAssertionItemDecl kDeclared{item, {}, {}, nullptr};
      if (item->kind == ModuleItemKind::kSequenceDecl) {
        made.emplace_back(VpiMakeSequenceDecl(kDeclared, kAt, kWith), item);
      } else if (item->kind == ModuleItemKind::kPropertyDecl) {
        made.emplace_back(VpiMakePropertyDecl(kDeclared, kAt, kWith), item);
      }
    }
    for (const auto& [declared, item] : made) {
      const VpiExprNames kBodyNames{objects,
                                    kPrefix,
                                    kNoGenBlocks,
                                    VpiFormalNames(declared, *item, ctx, build),
                                    &design.node_attrs,
                                    &kStand};
      VpiStmtBuild body = kWith;
      body.expression = [&](const Expr* expr) {
        return VpiGenBlockExpression(expr, kBodyNames, ctx, build);
      };
      VpiFillAssertionItemDeclBody(declared, *item, body);
    }
  }
}

VpiObject* VpiMakePropertyDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = MakeDeclHead(declared, vpiPropertyDecl, at, with.build);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    MakeDeclaredVariable(local, obj, at.ctx, with.build);
  }
  return obj;
}

VpiObject* VpiMakeSequenceDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = MakeDeclHead(declared, vpiSequenceDecl, at, with.build);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakeSeqFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.seq_linear.locals) {
    MakeDeclaredVariable(local, obj, at.ctx, with.build);
  }
  return obj;
}

VpiObject* VpiFormalNames(VpiObject* made, const ModuleItem& decl,
                          SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* names = build.alloc();
  names->parent = made;
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    VpiObject* stand = build.alloc();
    stand->type = vpiRefObj;
    stand->parent = made;
    stand->name = build.keep(std::string(decl.prop_formals[i]));
    stand->full_name = VpiScopedFullName(made, decl.prop_formals[i]);
    names->children.push_back(stand);
    if (!decl.prop_formal_is_local[i]) continue;
    const DataType& type = *decl.prop_formal_types[i];
    stand->type = FormalVariableKind(type, ctx);
    VpiMakeVarBits(*stand, type, DeclaredTypeWidth(type, ctx), ctx, build);
  }
  return names;
}

void VpiFillAssertionItemDeclBody(VpiObject* made, const ModuleItem& decl,
                                  const VpiStmtBuild& with) {
  if (made->type == vpiSequenceDecl) {
    made->body = SequenceDeclBody(decl, with);
    return;
  }
  const PropertyExprNode* tree = decl.prop_body_tree;
  if (tree == nullptr) return;
  VpiMakePropertySpecOf(
      made, VpiPropertySpecParts{decl.prop_clock, decl.prop_disable_iff, tree},
      with);
}

}  // namespace delta
