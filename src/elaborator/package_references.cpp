// §26.6 with §26.3: the names a package's declarations write, which decide
// what a wildcard import of it actually imported.

#include "elaborator/package_references.h"

#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

class ReferencedNames {
 public:
  std::unordered_set<std::string_view> names;

  void Expression(const Expr* e) {
    if (e == nullptr) return;
    names.insert(e->text);
    names.insert(e->callee);
    ForEachExprChild(e, [this](const Expr* child) { Expression(child); });
  }

  void Dims(Expr* left, Expr* right,
            const std::vector<std::pair<Expr*, Expr*>>& extra) {
    Expression(left);
    Expression(right);
    for (const auto& [l, r] : extra) {
      Expression(l);
      Expression(r);
    }
  }

  void Type(const DataType& t) {
    names.insert(t.type_name);
    Dims(t.packed_dim_left, t.packed_dim_right, t.extra_packed_dims);
    Expression(t.type_ref_expr);
    for (const EnumMember& m : t.enum_members) {
      Expression(m.value);
      Expression(m.range_start);
      Expression(m.range_end);
    }
    for (const StructMember& m : t.struct_members) {
      names.insert(m.type_name);
      Dims(m.packed_dim_left, m.packed_dim_right, m.extra_packed_dims);
      Expression(m.init_expr);
      for (const Expr* d : m.unpacked_dims) Expression(d);
      if (m.nested_type != nullptr) Type(*m.nested_type);
    }
    for (const DataType& p : t.type_params) Type(p);
  }

  void Statement(const Stmt* s) {
    if (s == nullptr) return;
    Type(s->var_decl_type);
    if (s->decl_item != nullptr) Item(s->decl_item);
    ForEachChildExpr(s, [this](const Expr* e) { Expression(e); });
    ForEachChildStmt(s, [this](const Stmt* sub) { Statement(sub); });
  }

  void Property(const PropertyExprNode* node) {
    if (node == nullptr) return;
    Expression(node->boolean);
    for (const auto* op : node->operands) Property(op);
  }

  void Class(const ClassDecl* cls) {
    names.insert(cls->base_class);
    for (const auto& [name, value] : cls->params) Expression(value);
    for (const ClassMember* m : cls->members) {
      Type(m->data_type);
      Expression(m->init_expr);
      for (const Expr* d : m->unpacked_dims) Expression(d);
      if (m->method != nullptr) Item(m->method);
      if (m->typedef_item != nullptr) Item(m->typedef_item);
    }
  }

  void Item(const ModuleItem* item) {
    Expression(item->init_expr);
    Type(item->data_type);
    Type(item->typedef_type);
    Type(item->return_type);
    for (const Expr* d : item->unpacked_dims) Expression(d);
    for (const FunctionArg& arg : item->func_args) {
      Type(arg.data_type);
      Expression(arg.default_value);
    }
    for (const Stmt* s : item->func_body_stmts) Statement(s);
    for (const EventExpr& ev : item->prop_clock) Expression(ev.signal);
    Expression(item->prop_disable_iff);
    Expression(item->prop_body_expr);
    Property(item->prop_body_tree);
    if (item->class_decl != nullptr) Class(item->class_decl);
  }
};

}  // namespace

std::unordered_set<std::string_view> PackageReferencedNames(
    const PackageDecl* pkg) {
  ReferencedNames walk;
  for (const ModuleItem* item : pkg->items) walk.Item(item);
  return std::move(walk.names);
}

}  // namespace delta
