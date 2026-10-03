#include <format>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser.h"

namespace delta {

// §23.10 / Syntax A.1.3 parameter_port_list: the collections being built up as
// each parameter_declaration / type_parameter_declaration in the list is
// parsed. These four references are the one accumulator object for the whole
// parameter port list, so the value- and type-parameter parsers share it.
struct ParamPortList {
  std::vector<std::pair<std::string_view, Expr*>>& params;
  std::unordered_set<std::string_view>& type_param_names;
  std::unordered_set<std::string_view>& localparam_port_names;
  std::vector<DataType>* param_types;
};

// What one parameter_port_declaration of A.1.3's parameter_port_list hands to
// the element after the comma. A.2.1.1's `parameter` and `localparam` each
// open a declaration whose list_of_param_assignments or
// list_of_type_assignments (A.2.3) runs on past commas, and `type` opens the
// second kind of list (printed pages 1174, 1181 and 1184 of IEEE
// 1800-2023): an element written with neither keyword nor a data type is
// another member of the list before it, and is a type parameter when that list
// is one of types.
struct ParamPortGroup {
  bool is_localparam = false;
  bool is_type = false;
};

// The parse of A.1.3's parameter_port_list, its value and its type
// parameter declarations, which a module, interface, program and class header
// share through Parser::ParseParamPortDecls.
struct ParserParamPortHelpers {
  // A type_parameter_declaration in a parameter_port_list. The `type` keyword
  // has already been consumed by the caller.
  static void ParseTypeParamPortDecl(Parser& p, ParamPortList& out,
                                     bool is_localparam_group) {
    // A type_parameter_declaration may carry an optional forward_type keyword
    // (enum, struct, union, class, or interface class) before the identifier
    // to restrict the kinds of type the parameter accepts.
    if (p.Match(TokenKind::kKwInterface)) {
      p.Expect(TokenKind::kKwClass, Subclause("6.20.3"));
    } else if (p.Check(TokenKind::kKwEnum) || p.Check(TokenKind::kKwStruct) ||
               p.Check(TokenKind::kKwUnion) || p.Check(TokenKind::kKwClass)) {
      p.Consume();
    }
    auto name = p.Expect(TokenKind::kIdentifier, Subclause("6.20.3"));
    bool has_default = false;
    DataType def_type;
    if (p.Match(TokenKind::kEq)) {
      has_default = true;
      if (p.Check(TokenKind::kKwType)) {
        p.ParseExpr();
      } else {
        def_type = p.ParseDataType();
      }
    }

    if (is_localparam_group && !has_default) {
      p.diag_.Error(name.loc,
                    std::format("localparam type '{}' in parameter port list "
                                "must have a default type",
                                name.text),
                    Subclause("6.20.1"));
    }
    out.params.push_back({name.text, nullptr});
    // §6.20.3: retain the default type (empty/kImplicit means no default).
    if (out.param_types) out.param_types->push_back(def_type);
    out.type_param_names.insert(name.text);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
    p.known_types_.insert(name.text);
  }

  // True at the type_identifier of a type_assignment (A.2.4) that continues
  // the list_of_type_assignments before it: a bare identifier -- a name the
  // parse knows as a type would open A.1.3's `data_type
  // list_of_param_assignments` instead -- followed by `=`, `,` or `)`, since
  // a type_assignment has no dimensions.
  static bool AtContinuedTypeAssignment(Parser& p) {
    if (!p.CheckIdentifier() ||
        p.known_types_.count(p.CurrentToken().text) != 0) {
      return false;
    }
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool continues = p.Check(TokenKind::kEq) || p.Check(TokenKind::kComma) ||
                     p.Check(TokenKind::kRParen);
    p.lexer_.RestorePos(saved);
    return continues;
  }

  // One element of A.1.3's parameter_port_list. `parameter`, `localparam`,
  // `type` and a data type each open a new parameter_port_declaration; a bare
  // identifier continues the list the element before it belongs to, so the
  // `T = uvm_void` of `#(type KEY = int, T = uvm_void)` declares a second type
  // parameter rather than a value parameter named T, and `T pool[KEY];` in
  // the body reads T as a type.
  static void ParseParamPortDecl(Parser& p, ParamPortList& out,
                                 ParamPortGroup& group) {
    if (p.Match(TokenKind::kKwLocalparam)) {
      group.is_localparam = true;
      group.is_type = false;
    } else if (p.Match(TokenKind::kKwParameter)) {
      group.is_localparam = false;
      group.is_type = false;
    }
    if (p.Match(TokenKind::kKwType)) {
      group.is_type = true;
    } else if (group.is_type && !AtContinuedTypeAssignment(p)) {
      group.is_type = false;
    }
    if (group.is_type) {
      ParseTypeParamPortDecl(p, out, group.is_localparam);
    } else {
      ParseValueParamPortDecl(p, out, group.is_localparam);
    }
  }

  // A value parameter declaration in a parameter_port_list.
  static void ParseValueParamPortDecl(Parser& p, ParamPortList& out,
                                      bool is_localparam_group) {
    DataType dtype = p.ParseDataType();
    p.ParseImplicitParamRange(dtype);
    auto name = p.Expect(TokenKind::kIdentifier, Subclause("6.20.2"));
    Expr* default_val = nullptr;
    if (p.Match(TokenKind::kEq)) {
      default_val = p.ParseExpr();
    }

    if (is_localparam_group && default_val == nullptr) {
      p.diag_.Error(name.loc,
                    std::format("localparam '{}' in parameter port list must "
                                "have a default value",
                                name.text),
                    Subclause("6.20.1"));
    }
    out.params.push_back({name.text, default_val});
    if (out.param_types) out.param_types->push_back(dtype);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
  }
};

// The parameter_port_declarations between the parentheses of A.1.3's
// parameter_port_list, which may be none; the caller reads the parentheses,
// whose subclause is its own.
void Parser::ParseParamPortDecls(
    std::vector<std::pair<std::string_view, Expr*>>& params,
    std::unordered_set<std::string_view>& type_param_names,
    std::unordered_set<std::string_view>& localparam_port_names,
    std::vector<DataType>* param_types) {
  if (Check(TokenKind::kRParen)) return;
  ParamPortList out{params, type_param_names, localparam_port_names,
                    param_types};
  ParamPortGroup group;
  do {
    ParserParamPortHelpers::ParseParamPortDecl(*this, out, group);
  } while (Match(TokenKind::kComma));
}

}  // namespace delta
