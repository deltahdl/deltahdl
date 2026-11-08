#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/param_port_list.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

struct ParamPortGroup {
  bool is_localparam = false;
  bool is_type = false;
};

struct ParserParamPortHelpers {
  static void ParseTypeParamPortDecl(Parser& p, ParamPortList& out,
                                     bool is_localparam_group) {
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
    if (out.locs) out.locs->push_back(name.loc);
    if (out.param_types) out.param_types->push_back(def_type);
    out.type_param_names.insert(name.text);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
    p.known_types_.insert(name.text);
  }

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

  static void ParseParamPortDecl(Parser& p, ParamPortList& out,
                                 ParamPortGroup& group) {
    if (p.Match(TokenKind::kKwLocalparam)) {
      group.is_localparam = true;
      group.is_type = false;
    } else if (p.Match(TokenKind::kKwParameter)) {
      group.is_localparam = false;
      group.is_type = false;
    }
    if (!ParserDataDeclHelpers::AtTypeReference(p) &&
        p.Match(TokenKind::kKwType)) {
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

  static void ParseValueParamPortDecl(Parser& p, ParamPortList& out,
                                      bool is_localparam_group) {
    DataType dtype;
    if (!ParserDataDeclHelpers::ReadTypeReference(p, dtype)) {
      dtype = p.ParseDeclaredDataType();
      p.ParseImplicitParamRange(dtype);
    }
    auto name = p.Expect(TokenKind::kIdentifier, Subclause("6.20.2"));
    if (p.Check(TokenKind::kLBracket)) {
      p.ParseUnpackedDims((*out.unpacked_dims)[name.text]);
    }
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
    if (out.locs) out.locs->push_back(name.loc);
    if (out.param_types) out.param_types->push_back(dtype);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
  }
};

void Parser::ParseParamPortDecls(ParamPortList& out) {
  if (Check(TokenKind::kRParen)) return;
  ParamPortGroup group;
  do {
    ParserParamPortHelpers::ParseParamPortDecl(*this, out, group);
  } while (Match(TokenKind::kComma));
}

}  // namespace delta
