#include <format>
#include <string>

#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

// A.5.4's udp_instance, `[ name_of_instance ] ( output_terminal ,
// input_terminal { , input_terminal } )`: two terminals at least, the first
// a net_lvalue under A.3.3. The parser had read the terminal list as any list
// of expressions and left both to elaboration, which reports the count for a
// primitive it resolves and the output terminal for none; each is now reported
// where the instance is read, the count under A.5.4 and the terminal under
// §28.3 as a gate's is, §29.8 having a UDP instantiated "in the same manner as
// gates".
ModuleItem* Parser::ParseOneUdpInstance(const Token& udp_tok, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kUdpInst;
  item->loc = loc;
  item->inst_module = udp_tok.text;

  ParseGateInstanceTail(*this, item,
                        CheckIdentifier() && !Check(TokenKind::kLParen));
  if (item->gate_terminals.size() < 2) {
    diag_.Error(loc,
                "a UDP instance connects an output terminal and at least one "
                "input terminal",
                Subclause("A.5.4"));
  }
  if (!item->gate_terminals.empty() && !IsNetLvalue(item->gate_terminals[0])) {
    diag_.Error(loc, "output terminal must be a net lvalue", Subclause("28.3"));
  }
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
    diag_.Error(loc, "UDP instantiation shall have at most two delays",
                Subclause("29.8"));
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
  Expect(TokenKind::kSemicolon, Subclause("29.8"));
}

void Parser::RejectUdpPortDimension() {
  if (!Check(TokenKind::kLBracket)) return;
  diag_.Error(CurrentLoc(),
              "UDP port shall be scalar; vector range not permitted",
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
  for (size_t i = 0; i < udp->table.size(); ++i) {
    for (size_t j = i + 1; j < udp->table.size(); ++j) {
      const auto& a = udp->table[i];
      const auto& b = udp->table[j];
      if (a.inputs == b.inputs && a.paren_edges == b.paren_edges &&
          a.current_state == b.current_state && a.output != b.output) {
        diag_.Error(udp->range.start,
                    "UDP table rows with identical inputs shall not specify "
                    "different outputs",
                    Subclause("29.3.4"));
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

// A.5.2: the one bit a 1-bit reg keeps of an integer literal written as its
// initial value, which is the literal's least significant bit under §10.7's
// truncation of an assignment to a narrower variable, or 'x' where that bit is
// unknown. The low bit of every base's value is the low bit of its last digit,
// so the literal's int_val answers it, and an x, z or ? as that last digit is
// the one spelling that leaves the bit unknown. 'x' for an expression that is
// not a literal: that bit is the run's to evaluate from UdpDecl::initial_expr.
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

// A.5.2 gives `[ = constant_expression ]` to `output reg port_identifier`
// alone; the `output port_identifier` alternative carries none. Reads the `=`
// the current token stands at and the expression after it, and returns the
// expression where the output was declared reg. After an output declared
// without reg the `=` is reported and the expression read past all the same,
// so the declaration is otherwise taken as written and the header's port count
// still agrees with the table below; nullptr is returned then.
Expr* Parser::ParseUdpOutputInitialValue(bool declares_reg) {
  auto eq_tok = Consume();
  Expr* value = ParseExpr();
  if (declares_reg) return value;
  diag_.Error(eq_tok.loc,
              "UDP output port takes an initial value only as 'output reg'",
              Subclause("A.5.2"));
  return nullptr;
}

void Parser::ParseUdpOutputDecl(UdpDecl* udp) {
  // Read into its own flag rather than off udp->is_sequential, which a
  // `reg q;` declared above this line has already set: A.5.2 puts the initial
  // value on the `output reg` form and not on an `output` that a separate
  // udp_reg_declaration makes sequential.
  bool declares_reg = Match(TokenKind::kKwReg);
  if (declares_reg) udp->is_sequential = true;
  RejectUdpPortDimension();
  auto id_tok = ExpectIdentifier(Subclause("29.3.2"));

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

// A.5.2 writes an initial value on udp_output_declaration's `output reg
// port_identifier [ = constant_expression ]` alone: udp_input_declaration is
// `input list_of_udp_port_identifiers` and udp_reg_declaration `reg
// variable_identifier`, and §29.4 gives the other place a sequential UDP's
// initial value stands, the initial statement. One written on either
// declaration is reported at its '=' and read past, so that the declaration
// ends at its own terminator.
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

// A.5.2's udp_input_declaration, `input list_of_udp_port_identifiers`, the
// `input` keyword consumed, read to its ';'. A.2.3 writes the list
// `port_identifier { , port_identifier }`, and A.9.3 spells the identifier
// `simple_identifier | escaped_identifier`.
void Parser::ParseUdpInputDecl(UdpDecl* udp) {
  do {
    RejectUdpPortDimension();
    udp->input_names.push_back(ExpectIdentifier(Subclause("29.3.2")).text);
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

// `row_is_sequential` says whether the row was written as A.5.3's
// `sequential_entry`, which is what decides where its fields are. Table 29-1
// permits `-` only in the output field of a sequential UDP, and a current-state
// field exists only in that form, so a row read as the other form has neither
// rule to answer.
static void ValidateUdpRowStateAndOutput(DiagEngine& diag,
                                         bool row_is_sequential,
                                         const UdpTableRow& row,
                                         SourceLoc row_loc) {
  if (row_is_sequential) {
    char cs = row.current_state;
    if (cs == '-') {
      diag.Error(row_loc, "- shall not appear in the current-state field",
                 Subclause("29.3.6"));
    } else if (UdpInputIsEdge(cs)) {
      diag.Error(row_loc,
                 "edge symbols shall not appear in the current-state field",
                 Subclause("29.3.6"));
    }
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

static void ValidateUdpTableRow(DiagEngine& diag, bool row_is_sequential,
                                const UdpTableRow& row, SourceLoc row_loc) {
  if (UdpRowContainsZ(row)) {
    diag.Error(row_loc, "UDP table row shall not contain z",
               Subclause("29.3.5"));
  }
  ValidateUdpRowInputTransitions(diag, row, row_loc);
  ValidateUdpRowStateAndOutput(diag, row_is_sequential, row, row_loc);
}

// §29.3.2 requires a UDP's two statements about its own form to agree:
// "Sequential UDPs shall contain a reg declaration for the output port" and
// "Combinational UDPs cannot contain a reg declaration". `udp->is_sequential`
// carries the first statement, the presence of a reg; `row_is_sequential`
// carries the second, the form the table entry was written in. Reports once per
// UDP, at the first row that disagrees, since one missing or surplus reg is one
// mistake however many rows stand under it.
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

// §29.3.4 reads a row's input fields off the header's port list by position:
// "The order of the input state fields of each row of the state table is taken
// directly from the port list in the UDP definition header", and it gives a row
// "one field per input and one field for the output". A row carrying some other
// number of fields therefore names no combination of this UDP's inputs at all.
// UdpRowMatchesLevels (src/simulator/udp_eval.cpp) answers no match for such a
// row whatever the inputs are, so the primitive falls to §29.3.4's default of
// "a default output state of x" and runs as though the row had not been
// written. Reports once per UDP, at the first row that disagrees, since one
// port list read wrong is one mistake however many rows stand under it.
//
// Says nothing where the header declared no inputs: ValidateUdpHeader has
// already reported that, every row would disagree with a port list that is not
// there, and the count this would name is the one already being reported.
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

// The symbols one token of a UDP input list stands for. A.5.3 writes
// level_input_list `level_symbol { level_symbol }` and edge_input_list
// `{ level_symbol } edge_indicator { level_symbol }` over single characters
// with no separator between them, so a run the lexer read as one token --
// `01` as a number, `x1` or `bx` as an identifier -- is every character of it,
// and a symbol outside level_symbol `0 | 1 | x | X | ? | b | B` and
// edge_symbol `r | R | f | F | p | P | n | N | *` is reported at the token and
// kept, so that the row's width still answers to the header. A `z` is left to
// §29.3.5's own report.
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

// One symbol of a UDP entry's current_state or next_state field, which A.5.3
// writes as a single level_symbol or output_symbol; a token of more than one
// character there is reported and its first character taken.
char Parser::ParseUdpFieldSymbol() {
  Token tok = Consume();
  if (tok.text.size() > 1) {
    diag_.Error(tok.loc,
                "a UDP entry's state and output fields are one symbol each",
                Subclause("A.5.3"));
  }
  return UdpCharFromToken(tok);
}

void Parser::ParseUdpTableRow(UdpDecl* udp, bool& reg_mismatch_reported,
                              bool& row_width_reported) {
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
      Expect(TokenKind::kRParen, Subclause("29.3.4"));
      while (row.paren_edges.size() < row.inputs.size()) {
        row.paren_edges.push_back({0, 0});
      }
      row.inputs.push_back('\x01');
      row.paren_edges.push_back({from, to});
    } else {
      AppendUdpInputSymbols(row, Consume());
    }
  }
  Expect(TokenKind::kColon, Subclause("29.3.4"));
  // A.5.3 tells the two entry forms apart by how many fields follow that colon:
  // `combinational_entry ::= level_input_list : output_symbol ;` writes one,
  // and `sequential_entry ::= seq_input_list : current_state : next_state ;`
  // writes two. Read the count off the row rather than off udp->is_sequential,
  // which records only how the output port was declared. The two are separate
  // statements about the same UDP, and comparing them is what
  // ValidateUdpRowAgainstRegDecl below does.
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
               "UDP output port shall be the first port in the port list",
               Subclause("29.3.1"));
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

// Says whether the parenthesized port list is A.5.2's
// `udp_declaration_port_list` rather than its `udp_port_list`. The two lists
// differ in what they hold and not in what order they hold it: the first holds
// `udp_output_declaration` and `udp_input_declaration` entries, each introduced
// by a direction keyword, and the second holds bare port identifiers. Choosing
// on the keyword rather than on `output` alone is what lets §29.3.1's "The
// output port shall be the first port in the port list" be reported against a
// list that declares its ports in the wrong order, rather than the leading
// `input` being reported as a port identifier gone missing. `inout` counts
// because §29.3.1 permits no such port on a UDP at all, so a list holding one
// is a declaration list with an illegal entry and never a list of names. `reg`
// does not: A.5.2 gives it no place at the head of an entry, only inside
// `udp_reg_declaration`, which is a `udp_port_declaration` written in the body.
bool Parser::UdpPortListIsDeclarations() {
  return Check(TokenKind::kKwOutput) || Check(TokenKind::kKwInput) ||
         Check(TokenKind::kKwInout);
}

// Parses A.5.2's `udp_declaration_port_list` through the closing parenthesis
// and the semicolon after it, reporting §29.3.1's two rules over the entries as
// they were written: "UDPs have multiple input ports and exactly one output
// port", and "The output port shall be the first port in the port list". Both
// header forms answer them in the same words, the second in
// ReconcileUdpNonAnsiPortList.
// Reads one entry of A.5.2's `udp_declaration_port_list` without placing it, so
// that what the entry declared is available to §29.3.1's rules before the
// UdpDecl is written to.
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
    Match(TokenKind::kKwInput);
  }
  // A.5.2 writes the optional `reg` and the optional initial value into
  // `udp_output_declaration` alone, so neither is read on an input entry.
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

// Places one entry of A.5.2's `udp_declaration_port_list` on `udp`, reporting
// §29.3.1's "UDPs have multiple input ports and exactly one output port" where
// a second output declaration arrives. Returns whether the entry was taken as
// the output port, which is not the same as whether it declared one.
static bool PlaceUdpAnsiPortEntry(DiagEngine& diag, UdpDecl* udp,
                                  const UdpAnsiPortEntry& entry) {
  bool is_output = entry.is_output;
  if (is_output && !udp->output_name.empty()) {
    diag.Error(entry.loc, "UDP shall have exactly one output port",
               Subclause("29.3.1"));
    // Take the surplus declaration's port as an input rather than dropping it.
    // It is a port the user wrote, and a header short one port disagrees with
    // the table below it for a second report about one mistake.
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
  do {
    UdpAnsiPortEntry entry = ParseUdpAnsiPortEntry();
    bool is_output = PlaceUdpAnsiPortEntry(diag_, udp, entry);
    // An inout entry is not a port §29.3.1 admits, and RejectUdpInoutPort has
    // already said so, so it is not what the output's position is measured
    // against.
    if (!have_first_port && !entry.is_inout) {
      have_first_port = true;
      first_port_is_output = is_output;
      first_port_loc = entry.loc;
    }
  } while (Match(TokenKind::kComma));

  // Held back until the whole list is read, and reported only where an output
  // was declared somewhere in it, so a list declaring none draws
  // ValidateUdpHeader's report about the missing output and not a second one
  // about where it should have stood.
  if (have_first_port && !first_port_is_output && !udp->output_name.empty()) {
    diag_.Error(first_port_loc,
                "UDP output port shall be the first port in the port list",
                Subclause("29.3.1"));
  }

  Expect(TokenKind::kRParen, Subclause("29.3.1"));
  Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
}

// Parses the non-ANSI header (a bare port-name list) followed by the separate
// port declarations, then reconciles the port-list order against them.
void Parser::ParseUdpNonAnsiHeader(UdpDecl* udp) {
  auto first_tok = ExpectIdentifier(Subclause("29.3.1"));
  std::string_view first_name = first_tok.text;
  SourceLoc first_loc = first_tok.loc;
  std::vector<std::string_view> port_list_inputs;
  while (Match(TokenKind::kComma)) {
    port_list_inputs.push_back(ExpectIdentifier(Subclause("29.3.1")).text);
  }
  Expect(TokenKind::kRParen, Subclause("29.3.1"));
  Expect(TokenKind::kSemicolon, Subclause("29.3.1"));
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
  auto id_tok = ExpectIdentifier(Subclause("29.3.3"));
  ValidateUdpInitialHeader(diag_, udp, scan, id_tok);
  Expect(TokenKind::kEq, Subclause("29.3.3"));

  auto rhs_tok = CurrentToken();
  udp->initial_value =
      ParseUdpInitialValue(TokenKind::kSemicolon, TokenKind::kSemicolon);
  if (!IsValidUdpInitialLiteral(rhs_tok.text)) {
    diag_.Error(rhs_tok.loc,
                "UDP initial statement RHS shall be 0, 1, or a single-bit "
                "literal",
                Subclause("29.3.3"));
  }
  Expect(TokenKind::kSemicolon, Subclause("29.3.3"));
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
    ParseAttributes();
    if (UdpPortListIsDeclarations()) {
      ParseUdpAnsiHeader(udp);
    } else {
      ParseUdpNonAnsiHeader(udp);
    }
  }

  if (Check(TokenKind::kKwInitial)) {
    // A.5.3 writes `[ udp_initial_statement ]` into sequential_body alone,
    // combinational_body opening with `table`; §29.4 has the statement give
    // "the initial value of the output" of a sequential UDP, and a
    // combinational UDP's output has no state to initialize.
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
  udp->range.start = CurrentLoc();
  Expect(TokenKind::kKwPrimitive, Subclause("29.3"));
  udp->name = ExpectIdentifier(Subclause("29.3.1")).text;

  Expect(TokenKind::kLParen, Subclause("29.3.1"));
  ParseAttributes();
  if (UdpPortListIsDeclarations()) {
    ParseUdpAnsiHeader(udp);
  } else {
    // A.5.1 gives `extern udp_nonansi_declaration` no `udp_port_declaration`
    // and no `udp_body`, so A.5.2's `udp_port_list` is the whole prototype: its
    // first name is the output port and the rest are inputs, and no separate
    // declarations exist to reconcile that order against.
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
