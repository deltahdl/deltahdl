#include <cstddef>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct PathShape {
  const DataType* type = nullptr;
  const std::vector<Expr*>* dims = nullptr;
  size_t next_dim = 0;
  bool dynamic_element = false;
};

using ShapeMap = std::unordered_map<std::string_view, PathShape>;

const ClassMember* FindClassProperty(const ClassDecl* cls,
                                     std::string_view name) {
  for (const ClassMember* m : cls->members)
    if (m->kind == ClassMemberKind::kProperty && m->name == name) return m;
  return nullptr;
}

class NbaDynamicElementWalk {
 public:
  NbaDynamicElementWalk(const NbaDynamicTables& tables,
                        const ShapeMap& module_vars, const ClassDecl* cls,
                        DiagEngine& diag)
      : tables_(tables), module_vars_(module_vars), cls_(cls), diag_(diag) {}

  void CheckBody(const std::vector<FunctionArg>& formals,
                 const std::vector<Stmt*>& body) {
    BodyDeclScopes scopes(false);
    for (const auto& arg : formals) scopes.DeclareFormal(arg);
    for (const Stmt* s : body) {
      scopes.Walk(s, [&](const Stmt* st) {
        if (st->kind != StmtKind::kNonblockingAssign) return;
        if (!WritesDynamicElement(st->lhs, scopes)) return;
        diag_.Error(
            st->range.start,
            "nonblocking assignment to element of dynamically sized array",
            Subclause("6.21"));
      });
    }
  }

 private:
  const std::vector<Expr*>* DimsOf(const DataType* type,
                                   const std::vector<Expr*>* own) const {
    if (!own->empty()) return own;
    if (type == nullptr) return own;
    auto it = tables_.shape.typedef_dims.find(type->type_name);
    return it == tables_.shape.typedef_dims.end() ? own : &it->second;
  }

  PathShape ShapeOf(const DataType* type, const std::vector<Expr*>* own) const {
    return PathShape{.type = type, .dims = DimsOf(type, own)};
  }

  std::optional<PathShape> ResolveName(std::string_view name,
                                       const BodyDeclScopes& scopes) const {
    if (const BodyDeclScopes::Decl* decl = scopes.Find(name))
      return ShapeOf(decl->type, decl->unpacked_dims);
    const ClassMember* prop =
        cls_ == nullptr ? nullptr : FindClassProperty(cls_, name);
    if (prop != nullptr) return ShapeOf(&prop->data_type, &prop->unpacked_dims);
    auto it = module_vars_.find(name);
    if (it == module_vars_.end()) return std::nullopt;
    return ShapeOf(it->second.type, it->second.dims);
  }

  std::optional<PathShape> ResolveMember(const DataType* type,
                                         std::string_view member) const {
    if (type == nullptr) return std::nullopt;
    if (const ClassDecl* cls = FindClassDecl(type->type_name, tables_.unit)) {
      const ClassMember* prop = FindClassProperty(cls, member);
      if (prop == nullptr) return std::nullopt;
      return ShapeOf(&prop->data_type, &prop->unpacked_dims);
    }
    std::vector<std::string_view> names;
    const DataType* agg = FollowTypedefs(*type, tables_.shape.typedefs, names);
    if (agg == nullptr) return std::nullopt;
    for (const StructMember& m : agg->struct_members) {
      if (m.name != member) continue;
      auto it = tables_.shape.typedefs.find(m.type_name);
      const DataType* member_type =
          it == tables_.shape.typedefs.end() ? m.nested_type : &it->second;
      return ShapeOf(member_type, &m.unpacked_dims);
    }
    return std::nullopt;
  }

  std::optional<PathShape> Resolve(const Expr* e,
                                   const BodyDeclScopes& scopes) const {
    if (e->kind == ExprKind::kIdentifier) return ResolveName(e->text, scopes);
    if (e->kind == ExprKind::kMemberAccess) {
      std::optional<PathShape> obj = Resolve(e->lhs, scopes);
      if (!obj) return std::nullopt;
      std::optional<PathShape> member = ResolveMember(obj->type, e->rhs->text);
      if (member) member->dynamic_element = obj->dynamic_element;
      return member;
    }
    if (e->kind != ExprKind::kSelect) return std::nullopt;
    std::optional<PathShape> shape = Resolve(e->base, scopes);
    if (!shape) return std::nullopt;
    if (shape->next_dim < shape->dims->size() &&
        !IsFixedSizeUnpackedDim((*shape->dims)[shape->next_dim], tables_.shape))
      shape->dynamic_element = true;
    ++shape->next_dim;
    return shape;
  }

  bool WritesDynamicElement(const Expr* e, const BodyDeclScopes& scopes) const {
    if (e->kind == ExprKind::kConcatenation) {
      for (const Expr* el : e->elements)
        if (WritesDynamicElement(el, scopes)) return true;
      return false;
    }
    std::optional<PathShape> shape = Resolve(e, scopes);
    return shape && shape->dynamic_element;
  }

  const NbaDynamicTables& tables_;
  const ShapeMap& module_vars_;
  const ClassDecl* cls_;
  DiagEngine& diag_;
};

void CheckItemBodies(const ModuleItem* item, NbaDynamicElementWalk& walk) {
  if (item->body != nullptr) walk.CheckBody({}, {item->body});
  walk.CheckBody(item->func_args, item->func_body_stmts);
}

}  // namespace

void CheckNbaDynamicElements(const ModuleDecl* decl,
                             const NbaDynamicTables& tables, DiagEngine& diag) {
  ShapeMap module_vars;
  for (const ModuleItem* top : decl->items) {
    ForEachItemAndGenerateDescendant(top, [&](const ModuleItem* item) {
      if (item->kind != ModuleItemKind::kVarDecl) return;
      module_vars.emplace(item->name, PathShape{.type = &item->data_type,
                                                .dims = &item->unpacked_dims});
    });
  }
  NbaDynamicElementWalk module_walk(tables, module_vars, nullptr, diag);
  for (const ModuleItem* top : decl->items) {
    ForEachItemAndGenerateDescendant(top, [&](const ModuleItem* item) {
      CheckItemBodies(item, module_walk);
      if (item->kind != ModuleItemKind::kClassDecl) return;
      NbaDynamicElementWalk class_walk(tables, module_vars, item->class_decl,
                                       diag);
      for (const ClassMember* m : item->class_decl->members)
        if (m->method != nullptr) CheckItemBodies(m->method, class_walk);
    });
  }
}

}  // namespace delta
