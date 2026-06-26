#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

ModuleItem* Parser::ParseOneUdpInstance(const Token& udp_tok, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kUdpInst;
  item->loc = loc;
  item->inst_module = udp_tok.text;

  ParseGateInstanceTail(*this, item,
                        CheckIdentifier() && !Check(TokenKind::kLParen));
  return item;
}

void Parser::ParseUdpInstList(const Token& udp_tok,
                              std::vector<ModuleItem*>& items) {
  auto loc = udp_tok.loc;

  uint8_t str0 = 0;
  uint8_t str1 = 0;
  TryParseStrengthSpec(str0, str1);

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* decay = nullptr;
  ParseGateDelay(delay, delay_fall, decay);

  if (decay != nullptr) {
    diag_.Error(loc, "UDP instantiation shall have at most two delays");
  }

  auto apply_common = [&](ModuleItem* item) {
    item->drive_strength0 = str0;
    item->drive_strength1 = str1;
    item->gate_delay = delay;
    item->gate_delay_fall = delay_fall;
  };

  auto* first = ParseOneUdpInstance(udp_tok, loc);
  apply_common(first);
  items.push_back(first);
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneUdpInstance(udp_tok, loc);
    apply_common(next);
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::RejectUdpPortDimension() {
  if (!Check(TokenKind::kLBracket)) return;
  diag_.Error(CurrentLoc(),
              "UDP port shall be scalar; vector range not permitted");
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
              "UDP ports shall be input or output; inout not permitted");
  Consume();
}

void Parser::ValidateUdpHeader(UdpDecl* udp) {
  if (udp->output_name.empty()) {
    diag_.Error(udp->range.start, "UDP shall have exactly one output port");
  }
  if (udp->input_names.empty()) {
    diag_.Error(udp->range.start, "UDP shall have at least one input port");
  }
}

void Parser::ValidateUdpTable(UdpDecl* udp) {
  for (size_t i = 0; i < udp->table.size(); ++i) {
    for (size_t j = i + 1; j < udp->table.size(); ++j) {
      const auto& a = udp->table[i];
      const auto& b = udp->table[j];
      if (a.inputs == b.inputs && a.paren_edges == b.paren_edges &&
          a.current_state == b.current_state && a.output != b.output) {
        diag_.Error(udp->range.start,
                    "UDP table rows with identical inputs shall not specify "
                    "different outputs");
        return;
      }
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

char Parser::ParseUdpInitialValue(TokenKind stop1, TokenKind stop2) {
  char result = '0';
  while (!Check(stop1) && !Check(stop2) && !AtEnd()) {
    auto tok = Consume();
    if (!tok.text.empty()) {
      char last = tok.text.back();
      if (last == '0' || last == '1' || last == 'x' || last == 'X') {
        result = (last == 'X') ? 'x' : last;
      }
    }
  }
  return result;
}

void Parser::ParseUdpOutputDecl(UdpDecl* udp) {
  if (Match(TokenKind::kKwReg)) {
    udp->is_sequential = true;
  }
  RejectUdpPortDimension();
  auto id_tok = Expect(TokenKind::kIdentifier);

  if (!udp->output_name.empty()) {
    diag_.Error(id_tok.loc, "UDP shall have exactly one output port");
  }
  udp->output_name = id_tok.text;
  if (Match(TokenKind::kEq)) {
    udp->has_initial = true;
    udp->initial_value =
        ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
  }
  Expect(TokenKind::kSemicolon);
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
      diag.Error(reg.loc, "UDP reg declaration shall name the output port");
    }
  }
}
}  // namespace

void Parser::ParseUdpPortDecls(UdpDecl* udp) {
  std::vector<PendingUdpReg> reg_decls;
  while (!Check(TokenKind::kKwTable) && !Check(TokenKind::kKwInitial) &&
         !AtEnd()) {
    ParseAttributes();
    if (Match(TokenKind::kKwOutput)) {
      ParseUdpOutputDecl(udp);
    } else if (Match(TokenKind::kKwInput)) {
      RejectUdpPortDimension();
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      while (Match(TokenKind::kComma)) {
        RejectUdpPortDimension();
        udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
      }
      Expect(TokenKind::kSemicolon);
    } else if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
      auto id_tok = Expect(TokenKind::kIdentifier);
      reg_decls.push_back({id_tok.text, id_tok.loc});
      Expect(TokenKind::kSemicolon);
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
               "UDP table row shall contain at most one input transition");
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
               "UDP table row with all-x inputs shall specify x output");
  }
}

static void ValidateUdpRowNoDashInput(DiagEngine& diag, const UdpTableRow& row,
                                      SourceLoc row_loc) {
  for (char c : row.inputs) {
    if (c == '-') {
      diag.Error(row_loc, "- shall not appear in a UDP input field");
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

static void ValidateUdpRowStateAndOutput(DiagEngine& diag, UdpDecl* udp,
                                         const UdpTableRow& row,
                                         SourceLoc row_loc) {
  if (udp->is_sequential) {
    char cs = row.current_state;
    if (cs == '-') {
      diag.Error(row_loc, "- shall not appear in the current-state field");
    } else if (UdpInputIsEdge(cs)) {
      diag.Error(row_loc,
                 "edge symbols shall not appear in the current-state field");
    }
  }

  {
    char out = row.output;
    bool ok = (out == '0' || out == '1' || out == 'x' || out == 'X');
    if (udp->is_sequential && out == '-') ok = true;
    if (!ok) {
      diag.Error(row_loc,
                 "UDP output field shall be 0, 1, or x (- is sequential only)");
    }
  }

  for (const auto& pe : row.paren_edges) {
    if (pe.first == 0 && pe.second == 0) continue;
    if (!UdpIsLevelSymbol(pe.first) || !UdpIsLevelSymbol(pe.second)) {
      diag.Error(row_loc,
                 "parenthesized edge endpoints shall be level symbols");
      break;
    }
  }
}

static void ValidateUdpTableRow(DiagEngine& diag, UdpDecl* udp,
                                const UdpTableRow& row, SourceLoc row_loc) {
  if (UdpRowContainsZ(row)) {
    diag.Error(row_loc, "UDP table row shall not contain z");
  }
  ValidateUdpRowInputTransitions(diag, row, row_loc);
  ValidateUdpRowStateAndOutput(diag, udp, row, row_loc);
}

void Parser::ParseUdpTableRow(UdpDecl* udp) {
  UdpTableRow row;
  SourceLoc row_loc = CurrentLoc();
  while (!Check(TokenKind::kColon) && !AtEnd()) {
    if (Check(TokenKind::kLParen)) {
      Consume();
      Token tok = Consume();
      char from = 0, to = 0;
      if (tok.text.size() >= 2) {
        from = tok.text[0];
        to = tok.text[1];
      } else {
        from = UdpCharFromToken(tok);
        to = UdpCharFromToken(Consume());
      }
      Expect(TokenKind::kRParen);
      while (row.paren_edges.size() < row.inputs.size()) {
        row.paren_edges.push_back({0, 0});
      }
      row.inputs.push_back('\x01');
      row.paren_edges.push_back({from, to});
    } else {
      row.inputs.push_back(UdpCharFromToken(Consume()));
    }
  }
  Expect(TokenKind::kColon);
  if (udp->is_sequential) {
    row.current_state = UdpCharFromToken(Consume());
    Expect(TokenKind::kColon);
  }
  row.output = UdpCharFromToken(Consume());
  Expect(TokenKind::kSemicolon);

  ValidateUdpTableRow(diag_, udp, row, row_loc);

  udp->table.push_back(row);
}

void Parser::ParseUdpTable(UdpDecl* udp) {
  Expect(TokenKind::kKwTable);
  while (!Check(TokenKind::kKwEndtable) && !AtEnd()) {
    ParseUdpTableRow(udp);
  }
  if (udp->table.empty()) {
    diag_.Error(CurrentLoc(), "UDP table shall contain at least one entry");
  }
  Expect(TokenKind::kKwEndtable);
}

// Validates that the non-ANSI port list's first port matches the declared
// output, then reorders udp->input_names to follow the order in which the
// inputs appeared in the parenthesized port list (only when every port-list
// input maps to a declared input).
static void ReconcileUdpNonAnsiPortList(
    DiagEngine& diag, UdpDecl* udp, std::string_view first_name,
    SourceLoc first_loc,
    const std::vector<std::string_view>& port_list_inputs) {
  if (!udp->output_name.empty() && !first_name.empty() &&
      first_name != udp->output_name) {
    diag.Error(first_loc,
               "UDP output port shall be the first port in the port list");
  }

  std::vector<std::string_view> reordered;
  reordered.reserve(port_list_inputs.size());
  for (auto name : port_list_inputs) {
    for (auto decl_name : udp->input_names) {
      if (decl_name == name) {
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
// The illegal syntactic forms scanned at the head of a UDP initial statement
// (IEEE 1800 §29.6): a leading begin keyword and a leading # delay control,
// each with the source position captured at the matching point in the token
// stream so a diagnostic can be emitted later.
struct UdpInitialHeaderScan {
  bool saw_begin = false;
  SourceLoc begin_loc;
  bool saw_hash = false;
  SourceLoc hash_loc;
};
}  // namespace

// Emits the diagnostics for a UDP initial statement header (the begin/delay
// form errors and the output-target mismatch) given the positions captured at
// the matching points in the token stream. Pure-diagnostic; no parsing.
static void ValidateUdpInitialHeader(DiagEngine& diag, const UdpDecl* udp,
                                     const UdpInitialHeaderScan& scan,
                                     const Token& id_tok) {
  if (scan.saw_begin) {
    diag.Error(scan.begin_loc,
               "UDP initial statement shall be a single procedural assignment");
  }
  if (scan.saw_hash) {
    diag.Error(scan.hash_loc,
               "UDP initial statement shall not contain delay control");
  }
  if (!udp->output_name.empty() && id_tok.text != udp->output_name) {
    diag.Error(id_tok.loc,
               "UDP initial statement shall target the output port");
  }
}

// Parses the ANSI-style header that begins with the output port declaration
// (output [reg] name [= initial], {input name}). Consumes through the closing
// parenthesis and the terminating semicolon.
void Parser::ParseUdpAnsiOutputHeader(UdpDecl* udp) {
  Consume();
  if (Match(TokenKind::kKwReg)) {
    udp->is_sequential = true;
  }
  RejectUdpPortDimension();
  udp->output_name = Expect(TokenKind::kIdentifier).text;
  if (Match(TokenKind::kEq)) {
    udp->has_initial = true;
    udp->initial_value =
        ParseUdpInitialValue(TokenKind::kComma, TokenKind::kRParen);
  }
  while (Match(TokenKind::kComma)) {
    ParseAttributes();
    if (Check(TokenKind::kKwInout)) {
      RejectUdpInoutPort();
    } else {
      Match(TokenKind::kKwInput);
    }
    RejectUdpPortDimension();
    udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
}

// Parses the non-ANSI header (a bare port-name list) followed by the separate
// port declarations, then reconciles the port-list order against them.
void Parser::ParseUdpNonAnsiHeader(UdpDecl* udp) {
  auto first_tok = Expect(TokenKind::kIdentifier);
  std::string_view first_name = first_tok.text;
  SourceLoc first_loc = first_tok.loc;
  std::vector<std::string_view> port_list_inputs;
  while (Match(TokenKind::kComma)) {
    port_list_inputs.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  ParseUdpPortDecls(udp);
  ReconcileUdpNonAnsiPortList(diag_, udp, first_name, first_loc,
                              port_list_inputs);
}

// Parses the optional UDP initial statement (initial out = literal;),
// validating its restricted form along the way.
void Parser::ParseUdpInitialStatement(UdpDecl* udp) {
  udp->has_initial = true;

  UdpInitialHeaderScan scan;
  scan.saw_begin = Check(TokenKind::kKwBegin);
  scan.begin_loc = CurrentLoc();
  scan.saw_hash = Check(TokenKind::kHash);
  scan.hash_loc = CurrentLoc();
  auto id_tok = Expect(TokenKind::kIdentifier);
  ValidateUdpInitialHeader(diag_, udp, scan, id_tok);
  Expect(TokenKind::kEq);

  auto rhs_tok = CurrentToken();
  udp->initial_value =
      ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
  if (!IsValidUdpInitialLiteral(rhs_tok.text)) {
    diag_.Error(rhs_tok.loc,
                "UDP initial statement RHS shall be 0, 1, or a single-bit "
                "literal");
  }
  Expect(TokenKind::kSemicolon);
}

UdpDecl* Parser::ParseUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kDotStar)) {
    Consume();
    Expect(TokenKind::kRParen);
    Expect(TokenKind::kSemicolon);
    ParseUdpPortDecls(udp);
  } else {
    ParseAttributes();
    if (Check(TokenKind::kKwInout)) {
      RejectUdpInoutPort();
    }
    if (Check(TokenKind::kKwOutput)) {
      ParseUdpAnsiOutputHeader(udp);
    } else {
      ParseUdpNonAnsiHeader(udp);
    }
  }

  if (Match(TokenKind::kKwInitial)) {
    ParseUdpInitialStatement(udp);
  }

  ParseUdpTable(udp);
  Expect(TokenKind::kKwEndprimitive);
  MatchEndLabel(udp->name);
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  ValidateUdpTable(udp);
  return udp;
}

UdpDecl* Parser::ParseExternUdpDecl() {
  auto* udp = arena_.Create<UdpDecl>();
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive);
  udp->name = Expect(TokenKind::kIdentifier).text;

  Expect(TokenKind::kLParen);
  ParseAttributes();
  if (Check(TokenKind::kKwInout)) {
    RejectUdpInoutPort();
  }
  if (Check(TokenKind::kKwOutput)) {
    Consume();
    if (Match(TokenKind::kKwReg)) {
      udp->is_sequential = true;
    }
    RejectUdpPortDimension();
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      ParseAttributes();
      if (Check(TokenKind::kKwInout)) {
        RejectUdpInoutPort();
      } else {
        Match(TokenKind::kKwInput);
      }
      RejectUdpPortDimension();
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  } else {
    udp->output_name = Expect(TokenKind::kIdentifier).text;
    while (Match(TokenKind::kComma)) {
      udp->input_names.push_back(Expect(TokenKind::kIdentifier).text);
    }
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  udp->range.end = CurrentLoc();
  ValidateUdpHeader(udp);
  return udp;
}

}  // namespace delta
