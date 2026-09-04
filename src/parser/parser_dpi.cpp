#include <cctype>
#include <format>
#include <string_view>

#include "common/types.h"
#include "parser/parser.h"
#include "parser/parser_dpi_validate.h"

namespace delta {

static bool IsValidCIdentifier(std::string_view text) {
  if (text.empty()) return false;
  auto first = static_cast<unsigned char>(text.front());
  if (!std::isalpha(first) && first != '_') return false;
  for (char ch : text.substr(1)) {
    auto c = static_cast<unsigned char>(ch);
    if (!std::isalnum(c) && c != '_') return false;
  }
  return true;
}

// §35.5.4: dpi_spec_string ::= "DPI-C" | "DPI". The lexer keeps the raw
// quoted text in the token; this returns the inner characters so the rest
// of the parser can compare against the two literal values from Syntax 35-1.
static std::string_view StripStringLiteralQuotes(std::string_view text) {
  if (text.size() < 2) return text;
  if (text.front() != '"' || text.back() != '"') return text;
  return text.substr(1, text.size() - 2);
}

// CPD-dedup: the dpi_spec_string parse and validation, the optional
// "= c_identifier" tail and the conformance of the linkage name are identical
// between a DPI import declaration and a DPI export declaration.
struct ParserDpiHelpers {
  static void ParseDpiSpecString(Parser& p, ModuleItem* item) {
    auto spec_tok = p.Consume();
    item->dpi_spec_string = StripStringLiteralQuotes(spec_tok.text);
    if (item->dpi_spec_string == "DPI") {
      // §35.5.4: "DPI" is deprecated; the warning text must point at the
      // canonical replacement and warn about possible C-code changes.
      p.diag_.Warning(
          spec_tok.loc,
          "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; "
          "use of the \"DPI-C\" string may require changes in the DPI "
          "application's C code",
          Subclause("35.5.4"));
    } else if (item->dpi_spec_string != "DPI-C") {
      p.diag_.Error(spec_tok.loc,
                    "DPI specification string must be \"DPI-C\" or \"DPI\"",
                    Subclause("35.5.4"));
    }
  }

  static void TryParseDpiCName(Parser& p, ModuleItem* item) {
    if (p.Check(TokenKind::kIdentifier)) {
      auto saved = p.lexer_.SavePos();
      auto tok = p.Consume();
      if (p.Match(TokenKind::kEq)) {
        if (!IsValidCIdentifier(tok.text)) {
          p.diag_.Error(tok.loc,
                        "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*",
                        Subclause("35.5.4"));
        }
        item->dpi_c_name = tok.text;
      } else {
        p.lexer_.RestorePos(saved);
      }
    }
  }

  // §35.5.4: with no explicit c_identifier the linkage name defaults to the
  // SystemVerilog subroutine name, and the clause requires conformance of a
  // linkage name reached "either directly or indirectly". §5.6 admits `$` in a
  // simple identifier, so a legal subroutine name is not always a legal C one.
  static void CheckDefaultedLinkageName(Parser& p, const ModuleItem* item,
                                        const Token& name_tok) {
    // Parser::Expect returns the token it did not get when the name is
    // missing, having already reported that. Reading a `;` back as a linkage
    // name would report a second time for the one mistake.
    if (name_tok.kind != TokenKind::kIdentifier &&
        name_tok.kind != TokenKind::kEscapedIdentifier) {
      return;
    }
    if (!item->dpi_c_name.empty()) return;
    if (IsValidCIdentifier(name_tok.text)) return;
    p.diag_.Error(
        name_tok.loc,
        std::format("DPI linkage name '{}', defaulted from the subroutine "
                    "name, must match [a-zA-Z_][a-zA-Z0-9_]*",
                    name_tok.text),
        Subclause("35.5.4"));
  }

  // Footnote 25 of Syntax 35-1: the dynamic_override_specifiers that
  // function_prototype and task_prototype admit "shall only be legal on method
  // declarations inside a non-interface class scope", and an import
  // declaration is never one. Consuming them here is what lets the report name
  // that rule rather than the identifier the parser went on to expect. The
  // message names the import declaration because §8.20 states the same rule
  // for an ordinary subroutine declaration and Elaborator reports it there:
  // one message reported under two clauses tells neither site apart, which is
  // what assert-subclause-citations fails a build for.
  static void RejectDynamicOverrideSpecifiers(Parser& p, ModuleItem* item) {
    auto loc = p.CurrentLoc();
    p.ParseDynamicOverrideSpecifiers(item);
    if (!item->is_method_initial && !item->is_method_extends &&
        !item->is_method_final) {
      return;
    }
    p.diag_.Error(loc,
                  "a DPI import declaration cannot carry "
                  "dynamic_override_specifiers, which are legal only on a "
                  "method declaration inside a non-interface class scope",
                  Subclause("35.5.4"));
  }
};

ModuleItem* Parser::ParseDpiImport() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiImport;
  item->loc = CurrentLoc();
  ParserDpiHelpers::ParseDpiSpecString(*this, item);

  if (Match(TokenKind::kKwPure)) {
    item->dpi_is_pure = true;
  }
  if (Match(TokenKind::kKwContext)) {
    item->dpi_is_context = true;
  }

  ParserDpiHelpers::TryParseDpiCName(*this, item);

  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction, Subclause("35.5.4"));
  }
  ParserDpiHelpers::RejectDynamicOverrideSpecifiers(*this, item);

  // §35.5.1.3: the pure property is reserved for imported functions; an
  // imported task can never be declared pure.
  if (item->dpi_is_task && item->dpi_is_pure) {
    diag_.Error(item->loc, "an imported task cannot be declared pure",
                Subclause("35.5.4"));
  }

  if (!item->dpi_is_task) {
    item->return_type = ParseDataType();
    ValidateDpiResultType(diag_, item);
  }
  auto name_tok = Expect(TokenKind::kIdentifier, Subclause("35.5.4"));
  item->name = name_tok.text;
  ParserDpiHelpers::CheckDefaultedLinkageName(*this, item, name_tok);

  if (Check(TokenKind::kLParen)) {
    in_dpi_import_formals_ = true;
    item->func_args = ParseFunctionArgs(false);
    in_dpi_import_formals_ = false;
  }
  ValidateDpiImportNoRefArgs(diag_, item);
  ValidateDpiImportFormalTypes(diag_, item);
  ValidateDpiImportOpenArrayPackedDims(diag_, item);
  Expect(TokenKind::kSemicolon, Subclause("35.5.4"));
  return item;
}

ModuleItem* Parser::ParseDpiExport(SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiExport;
  item->loc = loc;
  ParserDpiHelpers::ParseDpiSpecString(*this, item);

  ParserDpiHelpers::TryParseDpiCName(*this, item);

  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction, Subclause("35.7"));
  }
  auto name_tok = Expect(TokenKind::kIdentifier, Subclause("35.7"));
  item->name = name_tok.text;
  ParserDpiHelpers::CheckDefaultedLinkageName(*this, item, name_tok);
  Expect(TokenKind::kSemicolon, Subclause("35.7"));
  return item;
}

}  // namespace delta
