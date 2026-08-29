#include <utility>

#include "parser/parser.h"

namespace delta {

bool Parser::IsTimingCheckName(std::string_view name) {
  return name == "$setup" || name == "$hold" || name == "$setuphold" ||
         name == "$recovery" || name == "$removal" || name == "$recrem" ||
         name == "$width" || name == "$period" || name == "$skew" ||
         name == "$nochange" || name == "$timeskew" || name == "$fullskew";
}

ModuleItem* Parser::ParseSpecifyBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecifyBlock;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecify, Subclause("30.3"));

  while (!Check(TokenKind::kKwEndspecify) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseSpecifyItem(item->specify_items);
    // Missing endspecify: the enclosing endmodule reaches here and
    // ParseSpecifyItem's recovery consumes nothing. Stop and let the Expect
    // below report the missing endspecify rather than spinning.
    if (lexer_.SavePos().pos == before) break;
  }
  Expect(TokenKind::kKwEndspecify, Subclause("30.3"));
  return item;
}

void Parser::ParseSpecparamDecl(std::vector<ModuleItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam, Subclause("6.20.5"));

  Expr* packed_left = nullptr;
  Expr* packed_right = nullptr;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    packed_left = ParseExpr();
    Expect(TokenKind::kColon, Subclause("6.20.5"));
    packed_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("6.20.5"));
  }

  auto parse_one = [&]() {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kSpecparam;
    item->loc = kw_loc;
    item->data_type.packed_dim_left = packed_left;
    item->data_type.packed_dim_right = packed_right;
    item->name = Expect(TokenKind::kIdentifier, Subclause("6.20.5")).text;
    Expect(TokenKind::kEq, Subclause("6.20.5"));
    if (item->name.starts_with("PATHPULSE$")) {
      // The parentheses are optional, which Syntax 30-7 does not admit. §30.7.1
      // prints `PATHPULSE$ = 3;` in its own worked example and its prose reads
      // the 3 back off it -- "it acquires reject and error limit of 3, as
      // defined by the last PATHPULSE$ declaration" -- while Syntax 30-7 and
      // A.2.4 both parenthesize the limit list. The two disagree, and a source
      // written from the example has to parse. Without the parentheses there is
      // one limit and §30.7.1 makes it serve as both: "If only the reject limit
      // value is specified, it shall apply to both the reject limit and the
      // error limit." A comma after an unparenthesized limit opens the next
      // specparam of the declaration, so only the parenthesized form reads one.
      bool parenthesized = Match(TokenKind::kLParen);
      item->init_expr = ParseMinTypMaxExpr();
      if (parenthesized) {
        if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
        Expect(TokenKind::kRParen, Subclause("30.7.1"));
      }
    } else {
      item->init_expr = ParseMinTypMaxExpr();
    }
    items.push_back(item);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon, Subclause("6.20.5"));
}

void Parser::ParseSpecifyItem(std::vector<SpecifyItem*>& items) {
  // Recover from a malformed specify item by skipping tokens up to (and
  // including) the terminating semicolon, without crossing the block end.
  auto skip_to_item_end = [&]() {
    while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
           !Check(TokenKind::kKwEndspecify) &&
           !Check(TokenKind::kKwEndmodule)) {
      Consume();
    }
    Match(TokenKind::kSemicolon);
  };

  if (Check(TokenKind::kKwPulsestyleOnevent) ||
      Check(TokenKind::kKwPulsestyleOndetect)) {
    items.push_back(ParsePulsestyleDecl());
    return;
  }

  if (Check(TokenKind::kKwShowcancelled) ||
      Check(TokenKind::kKwNoshowcancelled)) {
    items.push_back(ParseShowcancelledDecl());
    return;
  }

  if (Check(TokenKind::kKwSpecparam)) {
    ParseSpecparamInSpecify(items);
    return;
  }

  // A system identifier is either a timing check or an erroneous system task.
  if (Check(TokenKind::kSystemIdentifier) &&
      IsTimingCheckName(CurrentToken().text)) {
    items.push_back(ParseTimingCheck());
    return;
  }
  if (Check(TokenKind::kSystemIdentifier)) {
    diag_.Error(CurrentLoc(), "system task cannot appear in specify block",
                Subclause("31.2"));
    skip_to_item_end();
    return;
  }

  // An 'if'/'ifnone' module path declaration.
  if (Check(TokenKind::kKwIfnone)) {
    items.push_back(ParseIfnonePathDecl());
    return;
  }
  if (Check(TokenKind::kKwIf)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("30.4.4"));
    auto* cond = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("30.4.4"));
    items.push_back(ParseConditionalPathDecl(cond));
    return;
  }

  if (Check(TokenKind::kLParen)) {
    items.push_back(ParseSpecifyPathDecl());
    return;
  }

  diag_.Error(CurrentLoc(), "unexpected token in specify block",
              Subclause("30.3"));
  skip_to_item_end();
}

static bool IsZorX(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z';
}

static bool IsZeroOrOne(char c) { return c == '0' || c == '1'; }

// Two-character edge descriptors are either (z|x, 0|1) or two distinct binary
// values (e.g. "01", "10").
static bool IsTwoCharEdgeDescriptor(std::string_view text) {
  if (text.size() != 2) return false;
  if (IsZorX(text[0]) && IsZeroOrOne(text[1])) return true;
  return IsZeroOrOne(text[0]) && IsZeroOrOne(text[1]) && text[0] != text[1];
}

static bool IsSingleBinaryDigit(std::string_view text) {
  return text.size() == 1 && IsZeroOrOne(text[0]);
}

static bool IsSingleZorX(std::string_view text) {
  return text.size() == 1 && IsZorX(text[0]);
}

static void CheckEdgeDescriptorCount(DiagEngine& diag, SourceLoc list_loc,
                                     std::size_t count) {
  if (count == 0) {
    diag.Error(list_loc,
               "edge-control specifier requires at least one edge_descriptor",
               Subclause("31.5"));
  }
  if (count > 6) {
    diag.Error(list_loc,
               "edge-control specifier accepts at most six edge_descriptors",
               Subclause("31.5"));
  }
}

// The zero_or_one and z_or_x halves of an edge_descriptor such as `0x` lex as
// two separate tokens, so they arrive split apart. Syntax 31-15 forbids
// embedded spaces within an edge_descriptor: the two halves shall be
// immediately adjacent in the source.
void Parser::ParseSplitEdgeDescriptor(
    char first, SourceLoc tok_loc,
    std::vector<std::pair<char, char>>& descriptors) {
  Consume();
  auto next_text = CurrentToken().text;
  auto next_loc = CurrentLoc();
  if (!Check(TokenKind::kIdentifier) || !IsSingleZorX(next_text)) {
    diag_.Error(tok_loc, "invalid edge_descriptor", Subclause("31.5"));
    return;
  }
  if (next_loc.line == tok_loc.line && next_loc.column == tok_loc.column + 1) {
    descriptors.push_back({first, next_text[0]});
  } else {
    diag_.Error(tok_loc, "edge_descriptor may not contain embedded spaces",
                Subclause("31.5"));
  }
  Consume();
}

void Parser::ParseEdgeDescriptorList(
    std::vector<std::pair<char, char>>& descriptors) {
  auto list_loc = CurrentLoc();
  do {
    if (Check(TokenKind::kRBracket)) break;
    auto text = CurrentToken().text;
    auto tok_loc = CurrentLoc();

    if ((Check(TokenKind::kIntLiteral) || Check(TokenKind::kIdentifier)) &&
        IsTwoCharEdgeDescriptor(text)) {
      descriptors.push_back({text[0], text[1]});
      Consume();
    } else if (Check(TokenKind::kIntLiteral) && IsSingleBinaryDigit(text)) {
      ParseSplitEdgeDescriptor(text[0], tok_loc, descriptors);
    } else {
      diag_.Error(tok_loc, "invalid edge_descriptor", Subclause("31.5"));
      Consume();
    }
  } while (Match(TokenKind::kComma));
  CheckEdgeDescriptorCount(diag_, list_loc, descriptors.size());
  Expect(TokenKind::kRBracket, Subclause("31.5"));
}

SpecifyEdge Parser::ParseSpecifyEdge(
    std::vector<std::pair<char, char>>* edge_descriptors) {
  if (Check(TokenKind::kKwPosedge)) {
    Consume();
    return SpecifyEdge::kPosedge;
  }
  if (Check(TokenKind::kKwNegedge)) {
    Consume();
    return SpecifyEdge::kNegedge;
  }
  if (Check(TokenKind::kKwEdge)) {
    Consume();
    if (edge_descriptors && Match(TokenKind::kLBracket)) {
      ParseEdgeDescriptorList(*edge_descriptors);
    }
    return SpecifyEdge::kEdge;
  }
  return SpecifyEdge::kNone;
}

SpecifyTerminal Parser::ParseSpecifyTerminal() {
  SpecifyTerminal term;
  term.name = Expect(TokenKind::kIdentifier, Subclause("30.4")).text;

  if (Match(TokenKind::kDot)) {
    term.interface_name = term.name;
    term.name = Expect(TokenKind::kIdentifier, Subclause("25.6")).text;
  }

  if (Match(TokenKind::kLBracket)) {
    term.range_left = ParseExpr();
    if (Match(TokenKind::kColon)) {
      term.range_kind = SpecifyRangeKind::kPartSelect;
      term.range_right = ParseExpr();
    } else if (Match(TokenKind::kPlusColon)) {
      term.range_kind = SpecifyRangeKind::kPlusIndexed;
      term.range_right = ParseExpr();
    } else if (Match(TokenKind::kMinusColon)) {
      term.range_kind = SpecifyRangeKind::kMinusIndexed;
      term.range_right = ParseExpr();
    } else {
      term.range_kind = SpecifyRangeKind::kBitSelect;
    }
    Expect(TokenKind::kRBracket, Subclause("30.4"));
  }

  return term;
}

void Parser::ParsePathPorts(std::vector<SpecifyTerminal>& ports) {
  if (Match(TokenKind::kLBrace)) {
    bool is_replication = false;
    if (!Check(TokenKind::kIdentifier)) {
      is_replication = true;
    } else {
      auto saved = lexer_.SavePos();
      Consume();
      is_replication = Check(TokenKind::kLBrace);
      lexer_.RestorePos(saved);
    }

    if (is_replication) {
      ParseExpr();
      Expect(TokenKind::kLBrace, Subclause("30.4.6"));
      ports.push_back(ParseSpecifyTerminal());
      while (Match(TokenKind::kComma)) {
        ports.push_back(ParseSpecifyTerminal());
      }
      Expect(TokenKind::kRBrace, Subclause("30.4.6"));
      Expect(TokenKind::kRBrace, Subclause("30.4.6"));
      return;
    }

    ports.push_back(ParseSpecifyTerminal());
    while (Match(TokenKind::kComma)) {
      ports.push_back(ParseSpecifyTerminal());
    }
    Expect(TokenKind::kRBrace, Subclause("30.4.6"));
    return;
  }
  ports.push_back(ParseSpecifyTerminal());
  while (Match(TokenKind::kComma)) {
    ports.push_back(ParseSpecifyTerminal());
  }
}

void Parser::ParsePathDelays(std::vector<Expr*>& delays) {
  auto loc = CurrentLoc();
  if (Match(TokenKind::kLParen)) {
    delays.push_back(ParseMinTypMaxExpr());
    while (Match(TokenKind::kComma)) {
      delays.push_back(ParseMinTypMaxExpr());
    }
    Expect(TokenKind::kRParen, Subclause("30.5"));
  } else {
    delays.push_back(ParseMinTypMaxExpr());
  }

  auto n = delays.size();
  if (n != 1 && n != 2 && n != 3 && n != 6 && n != 12) {
    diag_.Error(loc, "path delay must have 1, 2, 3, 6, or 12 values",
                Subclause("30.5"));
  }
}

SpecifyPolarity Parser::ParseSpecifyPolarity() {
  if (Check(TokenKind::kPlus)) {
    Consume();
    return SpecifyPolarity::kPositive;
  }
  if (Check(TokenKind::kMinus)) {
    Consume();
    return SpecifyPolarity::kNegative;
  }
  return SpecifyPolarity::kNone;
}

// Every parallel ('=>') form — plain, edge-sensitive, or with a data-source
// expression — is described with a single input and a single output terminal
// descriptor. Only the full ('*>') forms accept terminal lists.
static void CheckParallelPathTerminalCount(DiagEngine& diag, SourceLoc loc,
                                           const SpecifyPathDecl& path) {
  if (path.path_kind == SpecifyPathKind::kParallel &&
      (path.src_ports.size() != 1 || path.dst_ports.size() != 1)) {
    diag.Error(loc,
               "parallel path '=>' requires a single source and "
               "destination terminal",
               Subclause("30.4.5"));
  }
}

// Maps a leading '+='/'-=' token to the polarity of a polarity-prefixed
// '+=>'/'-=>' parallel-path operator, or kNone when it is not a candidate.
static SpecifyPolarity PolarityPrefixOf(TokenKind kind) {
  if (kind == TokenKind::kPlusEq) return SpecifyPolarity::kPositive;
  if (kind == TokenKind::kMinusEq) return SpecifyPolarity::kNegative;
  return SpecifyPolarity::kNone;
}

// Consume the polarity-prefixed '+=>'/'-=>' spelling, whose polarity is lexed
// as a single '+='/'-=' token followed by '>'. Returns true (recording the
// polarity and parallel kind) only on a complete match; a partial match
// restores the saved position so the plain operators are reconsidered.
bool Parser::ParsePolarityPrefixedParallelPath(SpecifyItem* item) {
  SpecifyPolarity prefix = PolarityPrefixOf(CurrentToken().kind);
  if (item->path.polarity != SpecifyPolarity::kNone ||
      prefix == SpecifyPolarity::kNone) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();
  if (Match(TokenKind::kGt)) {
    item->path.polarity = prefix;
    item->path.path_kind = SpecifyPathKind::kParallel;
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

// Consume the path operator that separates source and destination terminals.
void Parser::ParseSpecifyPathOperator(SpecifyItem* item) {
  if (ParsePolarityPrefixedParallelPath(item)) return;
  if (Match(TokenKind::kEqGt)) {
    item->path.path_kind = SpecifyPathKind::kParallel;
  } else if (Match(TokenKind::kStarGt)) {
    item->path.path_kind = SpecifyPathKind::kFull;
  } else {
    Consume();
  }
}

// Parse the destination terminal descriptor, which is parenthesized only when
// it carries a destination polarity and data-source expression. §30.4.3: the
// output polarity operator sits between the output terminal and the
// data-source ':' separator. When written with no space it abuts the colon, so
// '+:' / '-:' lex as a single token and the polarity and separator are
// recovered from it; a space (e.g. 'q + : d') instead leaves a plain polarity
// token followed by ':'.
void Parser::ParseSpecifyPathDestination(SpecifyItem* item) {
  bool parenthesized = Match(TokenKind::kLParen);
  ParsePathPorts(item->path.dst_ports);
  if (!parenthesized) return;
  if (Match(TokenKind::kPlusColon)) {
    item->path.dst_polarity = SpecifyPolarity::kPositive;
  } else if (Match(TokenKind::kMinusColon)) {
    item->path.dst_polarity = SpecifyPolarity::kNegative;
  } else {
    item->path.dst_polarity = ParseSpecifyPolarity();
    Expect(TokenKind::kColon, Subclause("30.4.3"));
  }
  item->path.data_source = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("30.4.3"));
}

SpecifyItem* Parser::ParseSpecifyPathDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPathDecl;
  item->loc = CurrentLoc();

  Expect(TokenKind::kLParen, Subclause("30.4"));
  item->path.edge = ParseSpecifyEdge();
  ParsePathPorts(item->path.src_ports);

  item->path.polarity = ParseSpecifyPolarity();
  ParseSpecifyPathOperator(item);
  ParseSpecifyPathDestination(item);

  Expect(TokenKind::kRParen, Subclause("30.4"));
  Expect(TokenKind::kEq, Subclause("30.5"));
  ParsePathDelays(item->path.delays);
  Expect(TokenKind::kSemicolon, Subclause("30.4"));

  CheckParallelPathTerminalCount(diag_, item->loc, item->path);

  return item;
}

SpecifyItem* Parser::ParseConditionalPathDecl(Expr* cond) {
  auto* item = ParseSpecifyPathDecl();
  item->path.condition = cond;
  return item;
}

SpecifyItem* Parser::ParseIfnonePathDecl() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwIfnone, Subclause("30.4.4.4"));
  auto* item = ParseSpecifyPathDecl();
  item->path.is_ifnone = true;

  if (item->path.edge != SpecifyEdge::kNone ||
      item->path.data_source != nullptr) {
    diag_.Error(loc, "ifnone requires a simple path declaration",
                Subclause("30.4.4.4"));
  }
  return item;
}

TimingCheckKind Parser::ParseTimingCheckKind(std::string_view name) {
  if (name == "$setup") return TimingCheckKind::kSetup;
  if (name == "$hold") return TimingCheckKind::kHold;
  if (name == "$setuphold") return TimingCheckKind::kSetuphold;
  if (name == "$recovery") return TimingCheckKind::kRecovery;
  if (name == "$removal") return TimingCheckKind::kRemoval;
  if (name == "$recrem") return TimingCheckKind::kRecrem;
  if (name == "$width") return TimingCheckKind::kWidth;
  if (name == "$period") return TimingCheckKind::kPeriod;
  if (name == "$skew") return TimingCheckKind::kSkew;
  if (name == "$nochange") return TimingCheckKind::kNochange;
  if (name == "$timeskew") return TimingCheckKind::kTimeskew;
  if (name == "$fullskew") return TimingCheckKind::kFullskew;
  return TimingCheckKind::kSetup;
}

static bool NeedsDataSignal(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kSkew:
    case TimingCheckKind::kNochange:
    case TimingCheckKind::kTimeskew:
    case TimingCheckKind::kFullskew:
      return true;
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
      return false;
  }
  return false;
}

bool Parser::CheckNextIsCommaOrRParen() {
  auto saved = lexer_.SavePos();
  Consume();
  bool result = Check(TokenKind::kComma) || Check(TokenKind::kRParen);
  lexer_.RestorePos(saved);
  return result;
}

void Parser::ParseTimingCheckTrailingArgs(TimingCheckDecl& tc) {
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kRParen)) break;

    // Some checks still expect a second timing_check_limit at this position
    // ($width's optional threshold; the mandatory pair of $setuphold/$recrem/
    // $fullskew; $nochange's start/end edge offsets). A bare identifier there
    // is that limit (e.g. a specparam-named constant offset), not the notifier.
    bool two_limit_check = tc.check_kind == TimingCheckKind::kWidth ||
                           tc.check_kind == TimingCheckKind::kSetuphold ||
                           tc.check_kind == TimingCheckKind::kRecrem ||
                           tc.check_kind == TimingCheckKind::kFullskew ||
                           tc.check_kind == TimingCheckKind::kNochange;
    bool needs_second_limit = two_limit_check && tc.limits.size() < 2;

    // $timeskew/$fullskew allow the notifier to be an empty placeholder while
    // the event_based_flag/remain_active_flag still follow (Syntax 31-10/31-11
    // and the worked examples). An omitted notifier surfaces here as a comma
    // with nothing to consume for it, so hand straight to the extended-argument
    // parser with the notifier left empty.
    bool has_flag_args = tc.check_kind == TimingCheckKind::kTimeskew ||
                         tc.check_kind == TimingCheckKind::kFullskew;
    if (!needs_second_limit && has_flag_args && Check(TokenKind::kComma)) {
      ParseExtendedTimingCheckArgs(tc);
      break;
    }

    if (!needs_second_limit && Check(TokenKind::kIdentifier) &&
        CheckNextIsCommaOrRParen()) {
      tc.notifier = Consume().text;
      ParseExtendedTimingCheckArgs(tc);
      break;
    }
    tc.limits.push_back(ParseMinTypMaxExpr());
  }
}

void Parser::ParseTimeskewExtendedArgs(TimingCheckDecl& tc) {
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.event_based_flag = ParseExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.remain_active_flag = ParseMinTypMaxExpr();
  }
}

void Parser::ParseOptionalDelayedRef(std::string_view& name, Expr*& expr) {
  if (!Check(TokenKind::kIdentifier)) return;
  name = Consume().text;
  if (Match(TokenKind::kLBracket)) {
    expr = ParseMinTypMaxExpr();
    Expect(TokenKind::kRBracket, Subclause("31.9"));
  }
}

void Parser::ParseSetupholdExtendedArgs(TimingCheckDecl& tc) {
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timestamp_cond = ParseMinTypMaxExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timecheck_cond = ParseMinTypMaxExpr();
  }
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  ParseOptionalDelayedRef(tc.delayed_ref, tc.delayed_ref_expr);
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  ParseOptionalDelayedRef(tc.delayed_data, tc.delayed_data_expr);
}

void Parser::ParseExtendedTimingCheckArgs(TimingCheckDecl& tc) {
  if (tc.check_kind == TimingCheckKind::kTimeskew ||
      tc.check_kind == TimingCheckKind::kFullskew) {
    ParseTimeskewExtendedArgs(tc);
    return;
  }

  if (tc.check_kind == TimingCheckKind::kSkew) {
    return;
  }
  ParseSetupholdExtendedArgs(tc);
}

// Checks that timing checks requiring two timing_check_limit arguments
// ($setuphold, $recrem, $fullskew) actually received them.
static void ValidateTimingCheckLimitCount(DiagEngine& diag, SourceLoc loc,
                                          const TimingCheckDecl& tc) {
  if (tc.limits.size() >= 2) return;

  if (tc.check_kind == TimingCheckKind::kSetuphold) {
    diag.Error(loc, "$setuphold requires two timing_check_limit arguments",
               Subclause("31.3.3"));
  } else if (tc.check_kind == TimingCheckKind::kRecrem) {
    diag.Error(loc, "$recrem requires two timing_check_limit arguments",
               Subclause("31.3.6"));
  } else if (tc.check_kind == TimingCheckKind::kFullskew) {
    diag.Error(loc, "$fullskew requires two timing_check_limit arguments",
               Subclause("31.4.3"));
  }
}

// Checks that $width and $period reference events carry an edge specification.
static void ValidateTimingCheckEdgeRequired(DiagEngine& diag, SourceLoc loc,
                                            const TimingCheckDecl& tc) {
  if (tc.ref_edge != SpecifyEdge::kNone) return;

  if (tc.check_kind == TimingCheckKind::kWidth) {
    diag.Error(loc, "$width reference_event must be an edge specification",
               Subclause("31.4.4"));
  } else if (tc.check_kind == TimingCheckKind::kPeriod) {
    diag.Error(loc, "$period reference_event must be an edge specification",
               Subclause("31.4.5"));
  }
}

// Checks the $nochange-specific argument-count and edge-kind requirements.
static void ValidateNochangeTimingCheck(DiagEngine& diag, SourceLoc loc,
                                        const TimingCheckDecl& tc) {
  if (tc.check_kind != TimingCheckKind::kNochange) return;

  if (tc.limits.size() < 2) {
    diag.Error(loc,
               "$nochange requires both start_edge_offset and "
               "end_edge_offset arguments",
               Subclause("31.4.6"));
  }
  if (tc.ref_edge != SpecifyEdge::kPosedge &&
      tc.ref_edge != SpecifyEdge::kNegedge) {
    diag.Error(loc,
               "$nochange reference_event must use posedge or negedge "
               "(edge-control specifiers are not allowed)",
               Subclause("31.4.6"));
  }
}

static void ValidateTimingCheckDecl(DiagEngine& diag, SourceLoc loc,
                                    const TimingCheckDecl& tc) {
  ValidateTimingCheckLimitCount(diag, loc, tc);
  ValidateTimingCheckEdgeRequired(diag, loc, tc);
  ValidateNochangeTimingCheck(diag, loc, tc);
}

SpecifyItem* Parser::ParseTimingCheck() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kTimingCheck;
  item->loc = CurrentLoc();
  // The check's own first token, which is the keyword §31.2's Syntax 31-1 opens
  // every system_timing_check production with. TimingCheckDecl::loc
  // (parser/ast_specify.h) is what carries it past the parse:
  // BuildTimingCheckUnderOptions (simulator/specify_timing_check.cpp) copies it
  // into TimingCheckEntry::loc, and that is where a §31 violation is reported.
  // A reader given the specify block's own position instead would be sent to
  // the block and left to guess which of its checks fired.
  item->timing_check.loc = item->loc;

  auto name = CurrentToken().text;
  item->timing_check.check_kind = ParseTimingCheckKind(name);
  Consume();

  Expect(TokenKind::kLParen, Subclause("31.2"));

  item->timing_check.ref_edge =
      ParseSpecifyEdge(&item->timing_check.ref_edge_descriptors);
  item->timing_check.ref_terminal = ParseSpecifyTerminal();
  if (Match(TokenKind::kAmpAmpAmp)) {
    item->timing_check.ref_condition = ParseExpr();
  }
  Expect(TokenKind::kComma, Subclause("31.2"));

  bool has_data_signal = NeedsDataSignal(item->timing_check.check_kind);
  if (has_data_signal) {
    item->timing_check.data_edge =
        ParseSpecifyEdge(&item->timing_check.data_edge_descriptors);
    item->timing_check.data_terminal = ParseSpecifyTerminal();
    if (Match(TokenKind::kAmpAmpAmp)) {
      item->timing_check.data_condition = ParseExpr();
    }
    Expect(TokenKind::kComma, Subclause("31.2"));
  }

  // §31.3.1 is the one check of Clause 31 that names its data event first.
  // Syntax 31-3 writes `$setup(data_event, reference_event, ...)` where Syntax
  // 31-4, 31-5, 31-6, 31-7 and 31-8 write the reference event first, and Tables
  // 31-1 through 31-6 say the same. The two terminals are read positionally
  // above, so without this a $setup arrives with each in the field named for
  // the other, and everything downstream -- BuildTimingCheckUnderOptions,
  // SdfAnnotationMatchesCheck and the §31.3 verdicts -- reads them by name.
  if (item->timing_check.check_kind == TimingCheckKind::kSetup) {
    std::swap(item->timing_check.ref_terminal,
              item->timing_check.data_terminal);
    std::swap(item->timing_check.ref_edge, item->timing_check.data_edge);
    std::swap(item->timing_check.ref_edge_descriptors,
              item->timing_check.data_edge_descriptors);
    std::swap(item->timing_check.ref_condition,
              item->timing_check.data_condition);
  }

  item->timing_check.limits.push_back(ParseMinTypMaxExpr());
  ParseTimingCheckTrailingArgs(item->timing_check);

  ValidateTimingCheckDecl(diag_, item->loc, item->timing_check);
  Expect(TokenKind::kRParen, Subclause("31.2"));
  Expect(TokenKind::kSemicolon, Subclause("31.2"));
  return item;
}

SpecifyItem* Parser::ParsePulsestyleDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPulsestyle;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwPulsestyleOndetect)) {
    item->is_ondetect = true;
  }
  Consume();

  item->signal_list.push_back(
      Expect(TokenKind::kIdentifier, Subclause("30.7.4.1")).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(
        Expect(TokenKind::kIdentifier, Subclause("30.7.4.1")).text);
  }
  Expect(TokenKind::kSemicolon, Subclause("30.7.4.1"));
  return item;
}

SpecifyItem* Parser::ParseShowcancelledDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kShowcancelled;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwNoshowcancelled)) {
    item->is_noshowcancelled = true;
  }
  Consume();

  item->signal_list.push_back(
      Expect(TokenKind::kIdentifier, Subclause("30.7.4.2")).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(
        Expect(TokenKind::kIdentifier, Subclause("30.7.4.2")).text);
  }
  Expect(TokenKind::kSemicolon, Subclause("30.7.4.2"));
  return item;
}

// Decode the input/output terminal names embedded in a "PATHPULSE$in$out"
// specparam name and mark the item as a PATHPULSE specparam.
static void DecodePathpulseName(SpecifyItem& sp) {
  sp.is_pathpulse = true;
  constexpr std::string_view kPrefix = "PATHPULSE$";
  std::string_view rest = sp.param_name.substr(kPrefix.size());
  if (rest.empty()) return;
  auto sep = rest.find('$');
  if (sep == std::string_view::npos) {
    sp.pathpulse_input = rest;
    return;
  }
  sp.pathpulse_input = rest.substr(0, sep);
  sp.pathpulse_output = rest.substr(sep + 1);
}

void Parser::ParseSpecparamInSpecify(std::vector<SpecifyItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam, Subclause("6.20.5"));

  if (Check(TokenKind::kLBracket)) {
    Consume();
    ParseExpr();
    Expect(TokenKind::kColon, Subclause("6.20.5"));
    ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("6.20.5"));
  }

  auto parse_pathpulse_value = [&](SpecifyItem* sp) {
    DecodePathpulseName(*sp);
    // The parentheses are optional here for the reason ParseSpecparamDecl above
    // states at length: §30.7.1's example writes `PATHPULSE$ = 3;` and Syntax
    // 30-7 parenthesizes. An unparenthesized limit leaves pathpulse_error null,
    // which is how §30.7.1's "it shall apply to both the reject limit and the
    // error limit" reaches ApplyPulseControlOverride in
    // src/simulator/specify_pulse.cpp -- that function takes a cleared
    // has_error as the instruction to use the reject limit for both.
    bool parenthesized = Match(TokenKind::kLParen);
    sp->pathpulse_reject = ParseMinTypMaxExpr();
    sp->param_value = sp->pathpulse_reject;
    if (parenthesized) {
      if (Match(TokenKind::kComma)) {
        sp->pathpulse_error = ParseMinTypMaxExpr();
      }
      Expect(TokenKind::kRParen, Subclause("30.7.1"));
    }
  };

  auto parse_one = [&]() {
    auto* sp = arena_.Create<SpecifyItem>();
    sp->kind = SpecifyItemKind::kSpecparam;
    sp->loc = kw_loc;
    sp->param_name = Expect(TokenKind::kIdentifier, Subclause("6.20.5")).text;
    Expect(TokenKind::kEq, Subclause("6.20.5"));
    if (sp->param_name.starts_with("PATHPULSE$")) {
      parse_pathpulse_value(sp);
    } else {
      sp->param_value = ParseMinTypMaxExpr();
    }
    items.push_back(sp);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon, Subclause("6.20.5"));
}

}  // namespace delta
