#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_module.h"

namespace delta {

class Parser;

bool IsBuiltinTypeKwForLocalVar(TokenKind k);

struct PortItemShape {
  explicit PortItemShape(const char* kind) : port(kind) {}

  const char* port;
  bool open = false;
  bool typed = false;
  bool named = false;
  bool in_tail = false;
  int dim_depth = 0;
  SourceLoc start;

  void Begin(const Token& tok);
  void NameFormal();
  void BeginDefault();
  bool SkipAttributes(Lexer& lexer);
  bool SkipTailToken(Lexer& lexer, DiagEngine& diag);
  void End(DiagEngine& diag);
};

void ParsePropertyPortList(Parser& parser, Lexer& lexer, DiagEngine& diag,
                           ModuleItem* item);

bool AtAssertionVariableDecl(
    Lexer& lexer, const std::unordered_set<std::string_view>& known_types);

bool VarWritesDataType(Lexer& lexer);
bool IsDisallowedLocalVarTypeKw(TokenKind k);
bool LexerCheck(Lexer& lexer, TokenKind kind);

void ReportChandleFormal(DiagEngine& diag, const Token& type_tok);

bool IsLocalVariableOfDecl(const ModuleItem* item, std::string_view name);

void ScanClockEventGroupForLocals(Lexer& lexer, DiagEngine& diag,
                                  const ModuleItem* item);

void ScanSystemDefaultValue(Lexer& lexer, DiagEngine& diag, ModuleItem* item,
                            bool clock_default_allowed);

}  // namespace delta
