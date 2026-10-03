// §20.6.1 (printed pages 628-629 of IEEE 1800-2023): $typename returns the
// resolved type of its argument, a data type or an expression, as a string
// built by the clause's steps: a typedef resolved back to the type it names
// (a), the default signing removed (b), a system-generated name for an
// anonymous structure, union or enumeration (c), a "$" for the name of an
// unpacked array (d), each enumeration constant's value appended (e), a
// user-defined type name prefixed with its scope (f), ranges as unsized
// decimals (g), and white space reduced to a single space between identifiers
// and keywords (h).

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// The keyword a built-in type is written with, empty for a type that is not
// one.
std::string_view BuiltinKeyword(DataTypeKind kind) {
  static const std::map<DataTypeKind, std::string_view> kKeywords = {
      {DataTypeKind::kLogic, "logic"},
      {DataTypeKind::kReg, "reg"},
      {DataTypeKind::kBit, "bit"},
      {DataTypeKind::kByte, "byte"},
      {DataTypeKind::kShortint, "shortint"},
      {DataTypeKind::kInt, "int"},
      {DataTypeKind::kLongint, "longint"},
      {DataTypeKind::kInteger, "integer"},
      {DataTypeKind::kTime, "time"},
      {DataTypeKind::kReal, "real"},
      {DataTypeKind::kShortreal, "shortreal"},
      {DataTypeKind::kRealtime, "realtime"},
      {DataTypeKind::kString, "string"},
      {DataTypeKind::kChandle, "chandle"},
      {DataTypeKind::kEvent, "event"}};
  auto it = kKeywords.find(kind);
  return it == kKeywords.end() ? std::string_view{} : it->second;
}

bool IsAggregateKind(DataTypeKind kind) {
  return kind == DataTypeKind::kEnum || kind == DataTypeKind::kStruct ||
         kind == DataTypeKind::kUnion;
}

// Step b: a vector type is unsigned by default, so only `signed` is written.
bool IsVectorKind(DataTypeKind kind) {
  return kind == DataTypeKind::kLogic || kind == DataTypeKind::kReg ||
         kind == DataTypeKind::kBit;
}

// What is written of a type: the parts a DataType and a StructMember share.
struct TypeParts {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  const Expr* left = nullptr;
  const Expr* right = nullptr;
  const std::vector<std::pair<Expr*, Expr*>>* extra = nullptr;
  std::string_view type_name;
  std::string_view scope_name;
  const DataType* whole = nullptr;
};

class TypenameWriter {
 public:
  TypenameWriter(SimContext& ctx, Arena& arena) : ctx_(ctx), arena_(arena) {}

  // `hint` names what declares the type -- a variable, a member -- and is
  // what an anonymous aggregate is named after (step c).
  std::string OfType(const DataType& type, std::string_view scope,
                     std::string_view hint) {
    return OfParts(PartsOf(type), scope, hint);
  }

  std::string OfMember(const StructMember& member, std::string_view scope) {
    if (member.nested_type != nullptr) {
      return OfType(*member.nested_type, scope, member.name);
    }
    TypeParts parts;
    parts.kind = member.type_kind;
    parts.is_signed = member.is_signed;
    parts.left = member.packed_dim_left;
    parts.right = member.packed_dim_right;
    parts.extra = &member.extra_packed_dims;
    parts.type_name = member.type_name;
    parts.scope_name = member.scope_name;
    return OfParts(parts, scope, member.name);
  }

 private:
  static TypeParts PartsOf(const DataType& type) {
    TypeParts parts;
    parts.kind = type.kind;
    parts.is_signed = type.is_signed;
    parts.left = type.packed_dim_left;
    parts.right = type.packed_dim_right;
    parts.extra = &type.extra_packed_dims;
    parts.type_name = type.type_name;
    parts.scope_name = type.scope_name;
    parts.whole = &type;
    return parts;
  }

  // Step g: each packed range as unsized decimal bounds.
  std::string PackedText(const TypeParts& parts) {
    std::string text;
    if (parts.left != nullptr && parts.right != nullptr) {
      text += RangeText(parts.left, parts.right);
    }
    for (const auto& [left, right] : *parts.extra) {
      text += RangeText(left, right);
    }
    return text;
  }

  std::string RangeText(const Expr* left, const Expr* right) {
    auto l = static_cast<int64_t>(EvalExpr(left, ctx_, arena_).ToUint64());
    auto r = static_cast<int64_t>(EvalExpr(right, ctx_, arena_).ToUint64());
    return "[" + std::to_string(l) + ":" + std::to_string(r) + "]";
  }

  std::string OfParts(const TypeParts& parts, std::string_view scope,
                      std::string_view hint) {
    if (parts.kind == DataTypeKind::kNamed) return OfName(parts, scope);
    if (parts.whole != nullptr && IsAggregateKind(parts.kind)) {
      return OfAggregate(*parts.whole, Anonymous(*parts.whole, scope, hint));
    }
    std::string text(BuiltinKeyword(parts.kind));
    if (text.empty()) text = "logic";
    if (IsVectorKind(parts.kind) && parts.is_signed) text += " signed";
    return text + PackedText(parts);
  }

  // Step a: a typedef name is resolved back to the type it names, the
  // declaration's own packed ranges written after it; step f: an aggregate
  // it names, and a class, keep the name, behind the scope declaring it.
  std::string OfName(const TypeParts& parts, std::string_view scope) {
    std::string prefix = parts.scope_name.empty()
                             ? std::string(scope)
                             : std::string(parts.scope_name) + "::";
    std::string key = parts.scope_name.empty()
                          ? std::string(parts.type_name)
                          : std::string(parts.scope_name) +
                                "::" + std::string(parts.type_name);
    const DataType* named = ctx_.FindTypeDeclaration(key);
    if (named == nullptr && parts.scope_name.empty()) {
      // §26.3: a name a package declares, made visible by an import.
      std::string_view imported = ctx_.FindPackageTypedefKey(parts.type_name);
      if (!imported.empty()) {
        named = ctx_.FindTypeDeclaration(imported);
        prefix = std::string(
            imported.substr(0, imported.size() - parts.type_name.size()));
      }
    }
    if (named == nullptr) return OfUnresolvedName(parts, prefix);
    if (IsAggregateKind(named->kind)) {
      return OfAggregate(
          *named, TypeOwnerPrefix(prefix) + std::string(parts.type_name));
    }
    return OfType(*named, prefix, parts.type_name) + PackedText(parts);
  }

  // A name no typedef resolves: a class, named behind the package or
  // compilation unit declaring it ("$unit::"), or the module; any other name
  // as written.
  std::string OfUnresolvedName(const TypeParts& parts,
                               const std::string& prefix) {
    if (parts.scope_name.empty()) {
      if (const ClassTypeInfo* cls = ctx_.FindClassType(parts.type_name)) {
        if (!cls->package.empty()) {
          return std::string(cls->package) + "::" + std::string(cls->name);
        }
      }
    }
    return TypeOwnerPrefix(prefix) + std::string(parts.type_name);
  }

  // Step f: a module's declarations are prefixed with the module's name and a
  // dot, a package's with the package and `::`.
  std::string TypeOwnerPrefix(std::string_view prefix) {
    if (!prefix.empty()) return std::string(prefix);
    return std::string(ctx_.CurrentScopeName()) + ".";
  }

  // Step c: an anonymous aggregate is named by the system. The clause leaves
  // the form to the implementation; this one writes "e$", "s$" or "u$"
  // followed by the name of what declares the type, which no other
  // declaration of the scope shares.
  std::string Anonymous(const DataType& type, std::string_view scope,
                        std::string_view hint) {
    char letter = type.kind == DataTypeKind::kEnum     ? 'e'
                  : type.kind == DataTypeKind::kStruct ? 's'
                                                       : 'u';
    return TypeOwnerPrefix(scope) + letter + "$" + std::string(hint);
  }

  std::string OfAggregate(const DataType& type, const std::string& name) {
    if (type.kind == DataTypeKind::kEnum) return OfEnum(type) + name;
    std::string text = type.kind == DataTypeKind::kStruct ? "struct" : "union";
    if (type.is_packed) text += " packed";
    text += "{";
    for (const StructMember& member : type.struct_members) {
      text += OfMember(member, "") + " " + std::string(member.name) + ";";
    }
    return text + "}" + name;
  }

  // Step e: each enumeration constant with its value, sized and signed as the
  // base type it is held in.
  std::string OfEnum(const DataType& type) {
    uint32_t width = 32;
    bool is_signed = true;
    if (type.enum_base_kind != DataTypeKind::kImplicit) {
      DataType base;
      base.kind = type.enum_base_kind;
      base.packed_dim_left = type.packed_dim_left;
      base.packed_dim_right = type.packed_dim_right;
      width = DeclaredTypeWidth(base, ctx_);
      is_signed = DeclaredTypeIsSigned(base, ctx_) || type.is_signed;
    }
    std::string text = "enum{";
    int64_t next = 0;
    for (size_t i = 0; i < type.enum_members.size(); ++i) {
      const EnumMember& member = type.enum_members[i];
      if (member.value != nullptr) {
        next = static_cast<int64_t>(
            EvalExpr(member.value, ctx_, arena_).ToUint64());
      }
      if (i > 0) text += ",";
      text += std::string(member.name) + "=" + std::to_string(width) +
              (is_signed ? "'sd" : "'d") + std::to_string(next);
      ++next;
    }
    return text + "}";
  }

  SimContext& ctx_;
  Arena& arena_;
};

// The declaration of the property `name` of the object's class or a class it
// derives from, null where none declares it.
const ClassMember* PropertyDeclaration(const ClassTypeInfo* type,
                                       std::string_view name) {
  for (; type != nullptr; type = type->parent) {
    if (type->decl == nullptr) continue;
    for (const ClassMember* member : type->decl->members) {
      if (member->kind == ClassMemberKind::kProperty && member->name == name) {
        return member;
      }
    }
  }
  return nullptr;
}

// A variable as $typename writes it: by the type its declaration recorded,
// or else by the kind the variable alone says it is; empty where neither
// says.
std::string TypenameOfVariable(const Variable& var, std::string_view name,
                               TypenameWriter& writer) {
  std::string unpacked(var.declared_unpacked);
  if (var.declared_type != nullptr) {
    return writer.OfType(*var.declared_type, var.declared_scope, name) +
           unpacked;
  }
  if (var.is_string) return "string" + unpacked;
  if (var.is_real) return "real" + unpacked;
  return {};
}

// What an identifier argument names, as $typename writes it: a variable, a
// property or a type parameter of the object a method runs on, a typedef
// name, or a built-in type keyword; empty where it names none of them.
std::string TypenameOfIdentifier(std::string_view name, SimContext& ctx,
                                 Arena& arena) {
  TypenameWriter writer(ctx, arena);
  if (const Variable* var = ctx.FindVariable(name)) {
    return TypenameOfVariable(*var, name, writer);
  }
  if (const ClassObject* self = ctx.CurrentThis()) {
    if (const ClassMember* member = PropertyDeclaration(self->type, name)) {
      return writer.OfType(member->data_type, "", name);
    }
    if (const DataType* actual =
            TypeParamActual(self, self->type->decl, name)) {
      return writer.OfType(*actual, "", name);
    }
  }
  if (ctx.FindTypeDeclaration(name) != nullptr ||
      !ctx.FindPackageTypedefKey(name).empty()) {
    DataType reference;
    reference.kind = DataTypeKind::kNamed;
    reference.type_name = name;
    return writer.OfType(reference, "", name);
  }
  return {};
}

// A select of one element of an unpacked array or queue, `q[0]` of a
// property `string q[$]` or of a variable `AB_t AB[10]`, as $typename writes
// it: the element type, which is the declared type without the dimension the
// select takes away; empty where `arg` is no such select.
std::string TypenameOfElement(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind != ExprKind::kSelect || arg->index_end != nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string_view name = arg->base->text;
  TypenameWriter writer(ctx, arena);
  if (const Variable* var = ctx.FindVariable(name)) {
    if (var->declared_type == nullptr || var->declared_unpacked.empty()) {
      return {};
    }
    std::string_view rest = var->declared_unpacked.substr(1);
    rest = rest.substr(rest.find(']') + 1);
    std::string suffix = rest.empty() ? "" : "$" + std::string(rest);
    return writer.OfType(*var->declared_type, var->declared_scope, name) +
           suffix;
  }
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return {};
  const ClassMember* member = PropertyDeclaration(self->type, name);
  if (member == nullptr || member->unpacked_dims.size() != 1) return {};
  return writer.OfType(member->data_type, "", name);
}

}  // namespace

Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "logic");
  const Expr* arg = expr->args[0];
  if (arg->kind == ExprKind::kTypeRef && arg->type_value != nullptr) {
    TypenameWriter writer(ctx, arena);
    return StringToLogic4Vec(arena,
                             writer.OfType(*arg->type_value, "", "type"));
  }
  std::string text = arg->kind == ExprKind::kIdentifier
                         ? TypenameOfIdentifier(arg->text, ctx, arena)
                         : TypenameOfElement(arg, ctx, arena);
  if (!text.empty()) return StringToLogic4Vec(arena, text);
  return EvalTypenameOfExpression(expr, ctx, arena);
}

}  // namespace delta
