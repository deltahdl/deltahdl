#include "elaborator/elaborator_dpi_formals.h"

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser_dpi_validate.h"

namespace delta {

namespace {

// §7.8: whether the unpacked dimension `dim` is an index type, which makes
// the declaration an associative array -- a keyword index type, the `*`
// wildcard, or a name the scope's typedefs or classes declare. A name the
// scope declares none of is a constant expression sizing the dimension
// (§7.4.2), a parameter among them, and is no index type.
bool IsAssocIndexDimension(const Expr* dim, const TypedefMap& typedefs,
                           const DpiClassNames& classes) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  std::string_view t = dim->text;
  if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
      t == "shortint" || t == "longint" || t == "bit" || t == "logic" ||
      t == "reg" || t == "time" || t == "*") {
    return true;
  }
  return typedefs.count(t) != 0 || classes.count(t) != 0;
}

}  // namespace

void CheckImportFormalTypedefTypes(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag) {
  for (const auto& arg : item->func_args) {
    if (arg.data_type.kind != DataTypeKind::kNamed) continue;
    if (NamesAClass(arg.data_type, typedefs, classes)) {
      diag.Error(item->loc,
                 std::format("formal argument '{}' has a class type, which "
                             "cannot be passed through the DPI",
                             arg.name),
                 Subclause("35.5.4"));
      continue;
    }
    DataType resolved = ResolveDpiTypeName(arg.data_type, typedefs);
    if (resolved.kind == DataTypeKind::kNamed) continue;
    DpiFormalTypeVerdict verdict = ClassifyDpiFormalType(resolved);
    if (verdict == DpiFormalTypeVerdict::kPermitted) continue;
    if (verdict == DpiFormalTypeVerdict::kUnpackedUnion) {
      diag.Error(
          item->loc,
          std::format("formal argument '{}' has type '{}', an unpacked union, "
                      "which is not permitted for a DPI imported subroutine; "
                      "only the packed form of a union is allowed",
                      arg.name, arg.data_type.type_name),
          Subclause("35.5.6"));
    } else {
      diag.Error(item->loc,
                 std::format("formal argument '{}' has type '{}', which is not "
                             "permitted for a DPI imported subroutine",
                             arg.name, arg.data_type.type_name),
                 Subclause("35.5.6"));
    }
    break;
  }
}

// §35.5.6: the name of the unpacked dimension kind that keeps `dim` from
// being a formal argument of a DPI subroutine -- "queue" for `[$]` (§7.10)
// and "associative" for an index type (§7.8) -- or empty for a sized
// dimension, which the subclause's unpacked array permits.
static std::string_view UnpermittedDimKind(const Expr* dim,
                                           const TypedefMap& typedefs,
                                           const DpiClassNames& classes) {
  if (dim == nullptr) return {};
  if (dim->kind == ExprKind::kIdentifier && dim->text == "$") return "queue";
  if (IsAssocIndexDimension(dim, typedefs, classes)) return "associative";
  return {};
}

void CheckImportFormalUnpackedDims(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag) {
  for (const auto& arg : item->func_args) {
    for (const Expr* dim : arg.unpacked_dims) {
      std::string_view kind = UnpermittedDimKind(dim, typedefs, classes);
      if (kind.empty()) continue;
      diag.Error(item->loc,
                 std::format("formal argument '{}' of a DPI imported "
                             "subroutine has {} {} dimension, which is not a "
                             "permitted formal argument type",
                             arg.name, kind == "queue" ? "a" : "an", kind),
                 Subclause("35.5.6"));
      return;
    }
  }
}

void CheckExportFormalUnpackedDims(const ModuleItem* callable,
                                   const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag) {
  std::string_view what =
      callable->kind == ModuleItemKind::kTaskDecl ? "task" : "function";
  for (const auto& arg : callable->func_args) {
    for (const Expr* dim : arg.unpacked_dims) {
      std::string_view kind = UnpermittedDimKind(dim, typedefs, classes);
      if (kind.empty()) continue;
      diag.Error(item->loc,
                 std::format("SystemVerilog {} '{}' has a formal argument "
                             "'{}' with {} {} dimension, which is not a "
                             "permitted formal argument type for DPI",
                             what, item->name, arg.name,
                             kind == "queue" ? "a" : "an", kind),
                 Subclause("35.5.6"));
      return;
    }
  }
}

}  // namespace delta
