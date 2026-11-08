#include <algorithm>
#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "parser/udp_ansi_port_entry.h"
#include "parser/udp_row_overlap.h"

namespace delta {

void Parser::RejectUdpPortDimension() {
  if (!Check(TokenKind::kLBracket)) return;
  diag_.Error(
      CurrentLoc(),
      "a UDP port carries a single bit, so it cannot take a vector range",
      Subclause("29.3.1"));
  int depth = 0;
  do {
    if (Check(TokenKind::kLBracket))
      ++depth;
    else if (Check(TokenKind::kRBracket))
      --depth;
    Consume();
  } while (depth > 0 && !AtEnd());
}

void Parser::RejectUdpInoutPort() {
  diag_.Error(CurrentLoc(),
              "UDP ports shall be input or output; inout not permitted",
              Subclause("29.3.1"));
  Consume();
}

void Parser::ValidateUdpHeader(UdpDecl* udp) {
  if (udp->output_name.empty()) {
    diag_.Error(udp->range.start, "UDP shall have exactly one output port",
                Subclause("29.3.1"));
  }
  if (udp->input_names.empty()) {
    diag_.Error(udp->range.start, "UDP shall have at least one input port",
                Subclause("29.3.1"));
  }
}

void Parser::ValidateUdpTable(UdpDecl* udp) {
  for (size_t j = 1; j < udp->table.size(); ++j) {
    for (size_t i = 0; i < j; ++i) {
      if (!UdpRowsConflict(udp->table[i], udp->table[j])) continue;
      diag_.Error(udp->table[j].loc,
                  "UDP table rows covering the same combination of inputs "
                  "shall not specify different outputs",
                  Subclause("29.3.4"));
      return;
    }
  }
}

static char UdpCharFromToken(const Token& tok) {
  if (tok.kind == TokenKind::kStar) return '*';
  if (tok.kind == TokenKind::kMinus) return '-';
  if (tok.kind == TokenKind::kQuestion) return '?';
  if (!tok.text.empty()) return tok.text[0];
  return '?';
}

static bool UdpInputIsEdge(char c) {
  if (c == 'r' || c == 'R' || c == 'f' || c == 'F') return true;
  if (c == 'p' || c == 'P' || c == 'n' || c == 'N') return true;
  if (c == '*' || c == '\x01') return true;
  return false;
}

static bool UdpSymbolIsZ(char c) { return c == 'z' || c == 'Z'; }

static bool UdpIsLevelSymbol(char c) {
  return c == '0' || c == '1' || c == 'x' || c == 'X' || c == '?' || c == 'b' ||
         c == 'B';
}

static bool IsValidUdpInitialLiteral(std::string_view text) {
  if (text == "0" || text == "1") return true;
  if (text.size() == 4 && text[0] == '1' && text[1] == '\'' &&
      (text[2] == 'b' || text[2] == 'B')) {
    char d = text[3];
    return d == '0' || d == '1' || d == 'x' || d == 'X';
  }
  return false;
}

static char UdpInitialLiteralBit(std::string_view text) {
  char last = text.back();
  return last == 'X' ? 'x' : last;
}

static char UdpLiteralInitialBit(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kIntegerLiteral) return 'x';
  if (!expr->text.empty()) {
    char last = expr->text.back();
    if (last == 'x' || last == 'X' || last == 'z' || last == 'Z' ||
        last == '?') {
      return 'x';
    }
  }
  return (expr->int_val & 1) != 0 ? '1' : '0';
}

Expr* Parser::ParseUdpOutputInitialValue(bool declares_reg) {
  auto eq_tok = Consume();
  Expr* value = ParseExpr();
  if (declares_reg) return value;
  diag_.Error(eq_tok.loc,
              "UDP output port takes an initial value only as 'output reg'",
              Subclause("A.5.2"));
  return nullptr;
}

static void ReportUdpPortRedeclared(DiagEngine& diag, const UdpDecl& udp,
                                    std::string_view name, SourceLoc loc,
                                    bool output_too) {
  const bool kInput =
      std::ranges::find(udp.input_names, name) != udp.input_names.end();
  if (!kInput && !(output_too && name == udp.output_name)) return;
  diag.Error(loc, std::format("redeclaration of primitive port '{}'", name),
             Subclause("3.13"));
}

void Parser::ParseUdpOutputDecl(UdpDecl* udp) {
  bool declares_reg = Match(TokenKind::kKwReg);
  if (declares_reg) udp->is_sequential = true;
  RejectUdpPortDimension();
  auto id_tok = ExpectIdentifier(Subclause("29.3.2"));
  ReportUdpPortRedeclared(diag_, *udp, id_tok.text, id_tok.loc, false);

  if (!udp->output_name.empty()) {
    diag_.Error(id_tok.loc, "UDP shall have exactly one output port",
                Subclause("29.3.1"));
  }
  udp->output_name = id_tok.text;
  if (Check(TokenKind::kEq)) {
    if (Expr* value = ParseUdpOutputInitialValue(declares_reg)) {
      udp->has_initial = true;
      udp->initial_expr = value;
      udp->initial_value = UdpLiteralInitialBit(value);
    }
  }
  Expect(TokenKind::kSemicolon, Subclause("29.3.2"));
}

namespace {
struct PendingUdpReg {
  std::string_view name;
  SourceLoc loc;
};

void ValidatePendingUdpRegs(DiagEngine& diag, const UdpDecl* udp,
                            const std::vector<PendingUdpReg>& reg_decls) {
  for (const auto& reg : reg_decls) {
    if (!udp->output_name.empty() && reg.name != udp->output_name) {
      diag.Error(reg.loc, "UDP reg declaration shall name the output port",
                 Subclause("29.3.2"));
    }
  }
}
}  // namespace

void Parser::RejectUdpInitialValueOn(const char* declaration) {
  if (!Check(TokenKind::kEq)) return;
  diag_.Error(CurrentLoc(),
              std::string(declaration) +
                  " takes no initial value; a UDP's is written on 'output "
                  "reg' or in its initial statement",
              Subclause("A.5.2"));
  Consume();
  ParseExpr();
}

void Parser::ParseUdpInputDecl(UdpDecl* udp) {
  do {
    RejectUdpPortDimension();
    const Token kId = ExpectIdentifier(Subclause("29.3.2"));
    ReportUdpPortRedeclared(diag_, *udp, kId.text, kId.loc, true);
    udp->input_names.push_back(kId.text);
    RejectUdpInitialValueOn("a UDP input declaration");
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("29.3.2"));
}

void Parser::ParseUdpPortDecls(UdpDecl* udp) {
  std::vector<PendingUdpReg> reg_decls;
  while (!Check(TokenKind::kKwTable) && !Check(TokenKind::kKwInitial) &&
         !AtEnd()) {
    ParseAttributes();
    if (Match(TokenKind::kKwOutput)) {
      ParseUdpOutputDecl(udp);
    } else if (Match(TokenKind::kKwInput)) {
      ParseUdpInputDecl(udp);
    } else if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
      auto id_tok = ExpectIdentifier(Subclause("29.3.2"));
      reg_decls.push_back({id_tok.text, id_tok.loc});
      RejectUdpInitialValueOn("a UDP reg declaration");
      Expect(TokenKind::kSemicolon, Subclause("29.3.2"));
    } else if (Check(TokenKind::kKwInout)) {
      RejectUdpInoutPort();

      while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
      Match(TokenKind::kSemicolon);
    } else {
      break;
    }
  }

  ValidatePendingUdpRegs(diag_, udp, reg_decls);
}

static bool UdpRowContainsZ(const UdpTableRow& row) {
  for (char c : row.inputs) {
    if (UdpSymbolIsZ(c)) return true;
  }
  for (const auto& pe : row.paren_edges) {
    if (UdpSymbolIsZ(pe.first) || UdpSymbolIsZ(pe.second)) return true;
  }
  return UdpSymbolIsZ(row.current_state) || UdpSymbolIsZ(row.output);
}

static void ValidateUdpRowEdgeCount(DiagEngine& diag, const UdpTableRow& row,
                                    SourceLoc row_loc) {
  int edge_count = 0;
  for (char c : row.inputs) {
    if (UdpInputIsEdge(c)) ++edge_count;
  }
  if (edge_count > 1) {
    diag.Error(row_loc,
               "UDP table row shall contain at most one input transition",
               Subclause("29.3.4"));
  }
}

static void ValidateUdpRowAllXInputs(DiagEngine& diag, const UdpTableRow& row,
                                     SourceLoc row_loc) {
  if (row.inputs.empty()) return;
  bool all_x = true;
  for (char c : row.inputs) {
    if (c != 'x' && c != 'X') {
      all_x = false;
      break;
    }
  }
  if (all_x && row.output != 'x' && row.output != 'X') {
    diag.Error(row_loc,
               "UDP table row with all-x inputs shall specify x output",
               Subclause("29.3.4"));
  }
}

static void ValidateUdpRowNoDashInput(DiagEngine& diag, const UdpTableRow& row,
                                      SourceLoc row_loc) {
  for (char c : row.inputs) {
    if (c == '-') {
      diag.Error(row_loc, "- shall not appear in a UDP input field",
                 Subclause("29.3.6"));
      break;
    }
  }
}

static void ValidateUdpRowInputTransitions(DiagEngine& diag,
                                           const UdpTableRow& row,
                                           SourceLoc row_loc) {
  ValidateUdpRowEdgeCount(diag, row, row_loc);
  ValidateUdpRowAllXInputs(diag, row, row_loc);
  ValidateUdpRowNoDashInput(diag, row, row_loc);
}

static void ValidateUdpRowCurrentState(DiagEngine& diag, char cs,
                                       SourceLoc row_loc) {
  if (cs == '-') {
    diag.Error(row_loc, "- shall not appear in the current-state field",
               Subclause("29.3.6"));
  } else if (UdpInputIsEdge(cs)) {
    diag.Error(row_loc,
               "edge symbols shall not appear in the current-state field",
               Subclause("29.3.6"));
  } else if (!UdpIsLevelSymbol(cs) && !UdpSymbolIsZ(cs)) {
    diag.Error(
        row_loc,
        "the current-state field holds a level symbol (0, 1, x, X, ?, b, B)",
        Subclause("29.3.6"));
  }
}

static void ValidateUdpRowStateAndOutput(DiagEngine& diag,
                                         bool row_is_sequential,
                                         const UdpTableRow& row,
                                         SourceLoc row_loc) {
  if (row_is_sequential) {
    ValidateUdpRowCurrentState(diag, row.current_state, row_loc);
  }

  {
    char out = row.output;
    bool ok = (out == '0' || out == '1' || out == 'x' || out == 'X');
    if (row_is_sequential && out == '-') ok = true;
    if (!ok) {
      diag.Error(row_loc,
                 "UDP output field shall be 0, 1, or x (- is sequential only)",
                 Subclause("29.3.6"));
    }
  }

  for (const auto& pe : row.paren_edges) {
    if (pe.first == 0 && pe.second == 0) continue;
    if (!UdpIsLevelSymbol(pe.first) || !UdpIsLevelSymbol(pe.second)) {
      diag.Error(row_loc, "parenthesized edge endpoints shall be level symbols",
                 Subclause("29.3.6"));
      break;
    }
  }
}

static bool UdpRowHasEdge(const UdpTableRow& row) {
  for (char c : row.inputs) {
    if (UdpInputIsEdge(c)) return true;
  }
  return false;
}

static void ValidateUdpTableRow(DiagEngine& diag, bool row_is_sequential,
                                const UdpTableRow& row, SourceLoc row_loc) {
  if (UdpRowContainsZ(row)) {
    diag.Error(row_loc, "UDP table row shall not contain z",
               Subclause("29.3.5"));
  }
  if (!row_is_sequential && UdpRowHasEdge(row)) {
    diag.Error(row_loc,
               "a combinational UDP entry's inputs are level symbols; an edge "
               "indicator belongs to a sequential entry",
               Subclause("29.3.4"));
  }
  ValidateUdpRowInputTransitions(diag, row, row_loc);
  ValidateUdpRowStateAndOutput(diag, row_is_sequential, row, row_loc);
}

static void ValidateUdpRowAgainstRegDecl(DiagEngine& diag, const UdpDecl* udp,
                                         bool row_is_sequential,
                                         SourceLoc row_loc,
                                         bool& already_reported) {
  if (row_is_sequential == udp->is_sequential || already_reported) return;
  already_reported = true;
  diag.Error(row_loc,
             row_is_sequential
                 ? "sequential UDP shall declare its output port reg"
                 : "combinational UDP shall not declare its output port reg",
             Subclause("29.3.2"));
}

static void ValidateUdpRowWidth(DiagEngine& diag, const UdpDecl* udp,
                                const UdpTableRow& row, SourceLoc row_loc,
                                bool& already_reported) {
  if (udp->input_names.empty() || already_reported) return;
  if (row.inputs.size() == udp->input_names.size()) return;
  already_reported = true;
  diag.Error(
      row_loc,
      std::format("UDP table row has {} input field(s) but primitive '{}' "
                  "declares {} input port(s)",
                  row.inputs.size(), udp->name, udp->input_names.size()),
      Subclause("29.3.4"));
}

void Parser::AppendUdpInputSymbols(UdpTableRow& row, const Token& tok) {
  if (tok.kind == TokenKind::kStar || tok.kind == TokenKind::kMinus ||
      tok.kind == TokenKind::kQuestion || tok.text.empty()) {
    row.inputs.push_back(UdpCharFromToken(tok));
    return;
  }
  for (char c : tok.text) {
    if (!UdpIsLevelSymbol(c) && !UdpInputIsEdge(c) && !UdpSymbolIsZ(c)) {
      diag_.Error(tok.loc,
                  "a UDP input field is a level_symbol (0, 1, x, X, ?, b, B) "
                  "or an edge_symbol (r, R, f, F, p, P, n, N, *)",
                  Subclause("A.5.3"));
    }
    row.inputs.push_back(c);
  }
}

char Parser::ParseUdpFieldSymbol() {
  Token tok = Consume();
  if (tok.text.size() > 1) {
    diag_.Error(tok.loc,
                "a UDP entry's state and output fields are one symbol each",
                Subclause("A.5.3"));
  }
  return UdpCharFromToken(tok);
}

void Parser::ParseUdpParenEdge(UdpTableRow& row) {
  SourceLoc loc = Consume().loc;
  std::string symbols;
  while (!Check(TokenKind::kRParen) && !Check(TokenKind::kColon) && !AtEnd()) {
    Token tok = Consume();
    if (tok.text.empty()) {
      symbols.push_back(UdpCharFromToken(tok));
    } else {
      symbols.append(tok.text);
    }
  }
  Expect(TokenKind::kRParen, Subclause("29.3.4"));
  if (symbols.size() != 2) {
    diag_.Error(loc, "an edge in parentheses is two level symbols",
                Subclause("29.3"));
    symbols.resize(2, '?');
  }
  while (row.paren_edges.size() < row.inputs.size()) {
    row.paren_edges.push_back({0, 0});
  }
  row.inputs.push_back('\x01');
  row.paren_edges.push_back({symbols[0], symbols[1]});
}

void Parser::ParseUdpTableRow(UdpDecl* udp, bool& reg_mismatch_reported,
                              bool& row_width_reported) {
  UdpTableRow row;
  SourceLoc row_loc = CurrentLoc();
  row.loc = row_loc;
  while (!Check(TokenKind::kColon) && !AtEnd()) {
    if (Check(TokenKind::kLParen)) {
      ParseUdpParenEdge(row);
    } else {
      AppendUdpInputSymbols(row, Consume());
    }
  }
  Expect(TokenKind::kColon, Subclause("29.3.4"));
  char first_field = ParseUdpFieldSymbol();
  bool row_is_sequential = Match(TokenKind::kColon);
  if (row_is_sequential) {
    row.current_state = first_field;
    row.output = ParseUdpFieldSymbol();
  } else {
    row.output = first_field;
  }
  Expect(TokenKind::kSemicolon, Subclause("29.3.4"));

  ValidateUdpRowAgainstRegDecl(diag_, udp, row_is_sequential, row_loc,
                               reg_mismatch_reported);
  ValidateUdpTableRow(diag_, row_is_sequential, row, row_loc);
  ValidateUdpRowWidth(diag_, udp, row, row_loc, row_width_reported);

  udp->table.push_back(row);
}

void Parser::ParseUdpTable(UdpDecl* udp) {
  Expect(TokenKind::kKwTable, Subclause("29.3.4"));
  bool reg_mismatch_reported = false;
  bool row_width_reported = false;
  while (!Check(TokenKind::kKwEndtable) && !AtEnd()) {
    ParseUdpTableRow(udp, reg_mismatch_reported, row_width_reported);
  }
  if (udp->table.empty()) {
    diag_.Error(CurrentLoc(), "UDP table shall contain at least one entry",
                Subclause("29.3.4"));
  }
  Expect(TokenKind::kKwEndtable, Subclause("29.3.4"));
}

static void MatchUdpNonAnsiPortList(DiagEngine& diag, const UdpDecl* udp,
                                    const Token& first,
                                    const std::vector<Token>& inputs) {
  auto listed = [&](std::string_view name, size_t before) {
    if (first.text == name) return true;
    return std::any_of(inputs.begin(),
                       inputs.begin() + static_cast<std::ptrdiff_t>(before),
                       [&](const Token& t) { return t.text == name; });
  };
  const auto& declared = udp->input_names;
  for (size_t i = 0; i < inputs.size(); ++i) {
    std::string_view name = inputs[i].text;
    if (listed(name, i)) {
      diag.Error(inputs[i].loc,
                 std::format("port '{}' appears more than once in the UDP's "
                             "port list",
                             name),
                 Subclause("29.3.2"));
    } else if (std::find(declared.begin(), declared.end(), name) ==
                   declared.end() &&
               name != udp->output_name) {
      diag.Error(inputs[i].loc,
                 std::format("port '{}' is listed in the UDP's port list but "
                             "never declared",
                             name),
                 Subclause("29.3.2"));
    }
  }
  for (std::string_view name : declared) {
    if (listed(name, inputs.size())) continue;
    diag.Error(first.loc,
               std::format("port '{}' is declared but missing from the UDP's "
                           "port list",
                           name),
               Subclause("29.3.2"));
  }
}

static void ReconcileUdpNonAnsiPortList(DiagEngine& diag, UdpDecl* udp,
                                        const Token& first,
                                        const std::vector<Token>& inputs) {
  MatchUdpNonAnsiPortList(diag, udp, first, inputs);
  std::string_view first_name = first.text;
  SourceLoc first_loc = first.loc;
  if (!udp->output_name.empty() && !first_name.empty() &&
      first_name != udp->output_name) {
    diag.Error(first_loc,
               "a UDP's output has to lead its port list, ahead of every input",
               Subclause("29.3.1"));
  }

  std::vector<std::string_view> reordered;
  reordered.reserve(inputs.size());
  for (const Token& tok : inputs) {
    for (auto decl_name : udp->input_names) {
      if (decl_name == tok.text) {
        reordered.push_back(decl_name);
        break;
      }
    }
  }
  if (reordered.size() == udp->input_names.size()) {
    udp->input_names = std::move(reordered);
  }
}

namespace {
struct UdpInitialHeaderScan {
  bool saw_begin = false;
  SourceLoc begin_loc;
  bool saw_hash = false;
  SourceLoc hash_loc;
};
}  // namespace

static void ValidateUdpInitialHeader(DiagEngine& diag, const UdpDecl* udp,
                                     const UdpInitialHeaderScan& scan,
                                     const Token& id_tok) {
  if (scan.saw_begin) {
    diag.Error(scan.begin_loc,
               "UDP initial statement shall be a single procedural assignment",
               Subclause("29.3.3"));
  }
  if (scan.saw_hash) {
    diag.Error(scan.hash_loc,
               "UDP initial statement shall not contain delay control",
               Subclause("29.7"));
  }
  if (!udp->output_name.empty() && id_tok.text != udp->output_name) {
    diag.Error(id_tok.loc, "UDP initial statement shall target the output port",
               Subclause("29.3.3"));
  }
}

bool Parser::UdpPortListIsDeclarations() {
  return Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInput) ||
         Check(TokenKind::kKwInout);
}

UdpAnsiPortEntry Parser::ParseUdpAnsiPortEntry() {
  UdpAnsiPortEntry entry;
  ParseAttributes();
  entry.loc = CurrentLoc();
  entry.is_inout = Check(TokenKind::kKwInout);
  if (entry.is_inout) {
    RejectUdpInoutPort();
  } else if (Match(TokenKind::kKwOutput)) {
    entry.is_output = true;
  } else {
    entry.keyword_omitted = !Match(TokenKind::kKwInput);
  }
  entry.declares_reg = entry.is_output && Match(TokenKind::kKwReg);
  RejectUdpPortDimension();
  entry.name = ExpectIdentifier(Subclause("29.3.1")).text;
  if (entry.is_output && Check(TokenKind::kEq)) {
    entry.initial_expr = ParseUdpOutputInitialValue(entry.declares_reg);
  } else if (!entry.is_output) {
    RejectUdpInitialValueOn("a UDP input declaration");
  }
  return entry;
}

static bool PlaceUdpAnsiPortEntry(DiagEngine& diag, UdpDecl* udp,
                                  const UdpAnsiPortEntry& entry) {
  ReportUdpPortRedeclared(diag, *udp, entry.name, entry.loc, true);
  bool is_output = entry.is_output;
  if (is_output && !udp->output_name.empty()) {
    diag.Error(entry.loc, "UDP shall have exactly one output port",
               Subclause("29.3.1"));
    is_output = false;
  }
  if (!is_output) {
    udp->input_names.push_back(entry.name);
    return false;
  }
  udp->output_name = entry.name;
  if (entry.declares_reg) udp->is_sequential = true;
  if (entry.initial_expr != nullptr) {
    udp->has_initial = true;
    udp->initial_expr = entry.initial_expr;
    udp->initial_value = UdpLiteralInitialBit(entry.initial_expr);
  }
  return true;
}

void Parser::ParseUdpAnsiHeader(UdpDecl* udp) {
  bool have_first_port = false;
  bool first_port_is_output = false;
  SourceLoc first_port_loc{};
  bool after_output = false;
  do {
    UdpAnsiPortEntry entry = ParseUdpAnsiPortEntry();
    if (entry.keyword_omitted && after_output) {
      diag_.Error(
          entry.loc,
          "the first input of a UDP's port list is declared with 'input'",
          Subclause("29.3"));
    }
    after_output = entry.is_output;
    bool is_output = PlaceUdpAnsiPortEntry(diag_, udp, entry);
    if (!have_first_port && !entry.is_inout) {
      have_first_port = true;
      first_port_is_output = is_output;
      first_port_loc = entry.loc;
    }
  } while (Match(TokenKind::kComma));

  if (have_first_port && !first_port_is_output && !udp->output_name.empty()) {
    diag_.Error(
        first_port_loc,
        "a UDP's output has to lead its port list, ahead of every input",
        Subclause("29.3.1"));
  }

  Expect(TokenKind::kRParen, Subclause("29.3.1"));
  Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
}

void Parser::ParseUdpNonAnsiHeader(UdpDecl* udp) {
  auto first_tok = ExpectIdentifier(Subclause("29.3.1"));
  std::vector<Token> port_list_inputs;
  while (Match(TokenKind::kComma)) {
    port_list_inputs.push_back(ExpectIdentifier(Subclause("29.3.1")));
  }
  Expect(TokenKind::kRParen, Subclause("29.3.1"));
  Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
  ParseUdpPortDecls(udp);
  ReconcileUdpNonAnsiPortList(diag_, udp, first_tok, port_list_inputs);
}

void Parser::ParseUdpInitialStatement(UdpDecl* udp) {
  udp->has_initial = true;

  UdpInitialHeaderScan scan;
  scan.saw_begin = Check(TokenKind::kKwBegin);
  scan.begin_loc = CurrentLoc();
  scan.saw_hash = Check(TokenKind::kHash);
  scan.hash_loc = CurrentLoc();
  auto id_tok = ExpectIdentifier(Subclause("29.3.3"));
  ValidateUdpInitialHeader(diag_, udp, scan, id_tok);
  Expect(TokenKind::kEq, Subclause("29.3.3"));

  auto rhs_tok = CurrentToken();
  if (!Check(TokenKind::kSemicolon)) Consume();
  bool one_literal =
      Check(TokenKind::kSemicolon) && IsValidUdpInitialLiteral(rhs_tok.text);
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
  udp->initial_value = one_literal ? UdpInitialLiteralBit(rhs_tok.text) : 'x';
  if (!one_literal) {
    diag_.Error(rhs_tok.loc,
                "UDP initial statement RHS shall be 0, 1, or a single-bit "
                "literal",
                Subclause("29.3.3"));
  }
  Expect(TokenKind::kSemicolon, Subclause("29.3.3"));
}

static void RejectAttributesBeforeUdpPortList(
    DiagEngine& diag, const std::vector<Attribute>& attrs) {
  if (attrs.empty()) return;
  diag.Error(attrs.front().loc,
             "a UDP's port list of names takes no attribute instance",
             Subclause("A.5.2"));
}

UdpDecl* Parser::ParseUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive, Subclause("29.3"));
  udp->name = ExpectIdentifier(Subclause("29.3.1")).text;

  Expect(TokenKind::kLParen, Subclause("29.3.1"));
  if (Check(TokenKind::kDotStar)) {
    Consume();
    Expect(TokenKind::kRParen, Subclause("29.3.1"));
    Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
    ParseUdpPortDecls(udp);
  } else {
    std::vector<Attribute> attrs = ParseAttributes();
    if (UdpPortListIsDeclarations()) {
      ParseUdpAnsiHeader(udp);
    } else {
      RejectAttributesBeforeUdpPortList(diag_, attrs);
      ParseUdpNonAnsiHeader(udp);
    }
  }

  if (Check(TokenKind::kKwInitial)) {
    if (!udp->is_sequential) {
      diag_.Error(CurrentLoc(),
                  "a UDP initial statement stands in a sequential body; a "
                  "combinational UDP's body opens with 'table'",
                  Subclause("A.5.3"));
    }
    Consume();
    ParseUdpInitialStatement(udp);
  }

  ParseUdpTable(udp);
  Expect(TokenKind::kKwEndprimitive, Subclause("29.3"));
  MatchEndLabel(udp->name);
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  ValidateUdpTable(udp);
  return udp;
}

UdpDecl* Parser::ParseExternUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->is_extern = true;
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive, Subclause("29.3"));
  udp->name = ExpectIdentifier(Subclause("29.3.1")).text;

  Expect(TokenKind::kLParen, Subclause("29.3.1"));
  std::vector<Attribute> attrs = ParseAttributes();
  if (UdpPortListIsDeclarations()) {
    ParseUdpAnsiHeader(udp);
  } else {
    RejectAttributesBeforeUdpPortList(diag_, attrs);
    udp->output_name = ExpectIdentifier(Subclause("29.3.1")).text;
    while (Match(TokenKind::kComma)) {
      udp->input_names.push_back(ExpectIdentifier(Subclause("29.3.1")).text);
    }
    Expect(TokenKind::kRParen, Subclause("29.3.1"));
    Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
  }
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  return udp;
}

}  // namespace delta
