#include "parser/parser.h"

namespace delta {

// Determine if a system identifier is a timing check keyword.
static bool IsTimingCheckName(std::string_view name) {
  return name == "$setup" || name == "$hold" || name == "$setuphold" ||
         name == "$recovery" || name == "$removal" || name == "$recrem" ||
         name == "$width" || name == "$period" || name == "$skew" ||
         name == "$nochange" || name == "$timeskew" || name == "$fullskew";
}

// Parse: specify ... endspecify
ModuleItem* Parser::ParseSpecifyBlock() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecifyBlock;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecify);

  while (!Check(TokenKind::kKwEndspecify) && !AtEnd()) {
    ParseSpecifyItem(item->specify_items);
  }
  Expect(TokenKind::kKwEndspecify);
  return item;
}

// Parse: specparam [range] name = expr {, name = expr} ;
ModuleItem* Parser::ParseSpecparamDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSpecparam;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam);

  // Optional packed dimension [msb:lsb]
  if (Check(TokenKind::kLBracket)) {
    Consume();
    item->data_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    item->data_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  item->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kEq);
  // pulse_control_specparam: PATHPULSE$ = ( reject [, error] ) (A.2.4)
  if (item->name.starts_with("PATHPULSE$")) {
    Expect(TokenKind::kLParen);
    item->init_expr = ParseMinTypMaxExpr();
    if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
    Expect(TokenKind::kRParen);
  } else {
    item->init_expr = ParseMinTypMaxExpr();
  }
  // list_of_specparam_assignments: skip additional assignments (A.2.1.1)
  while (Match(TokenKind::kComma)) {
    auto name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kEq);
    if (name.starts_with("PATHPULSE$")) {
      Expect(TokenKind::kLParen);
      ParseMinTypMaxExpr();
      if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      ParseMinTypMaxExpr();
    }
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

// Dispatch a single specify block item.
void Parser::ParseSpecifyItem(std::vector<SpecifyItem*>& items) {
  // pulsestyle_onevent / pulsestyle_ondetect
  if (Check(TokenKind::kKwPulsestyleOnevent) ||
      Check(TokenKind::kKwPulsestyleOndetect)) {
    items.push_back(ParsePulsestyleDecl());
    return;
  }
  // showcancelled / noshowcancelled
  if (Check(TokenKind::kKwShowcancelled) ||
      Check(TokenKind::kKwNoshowcancelled)) {
    items.push_back(ParseShowcancelledDecl());
    return;
  }
  // specparam inside specify block
  if (Check(TokenKind::kKwSpecparam)) {
    items.push_back(ParseSpecparamInSpecify());
    return;
  }
  // Timing checks: $setup, $hold, etc.
  if (Check(TokenKind::kSystemIdentifier)) {
    auto name = CurrentToken().text;
    if (IsTimingCheckName(name)) {
      items.push_back(ParseTimingCheck());
      return;
    }
  }
  // ifnone path
  if (Check(TokenKind::kKwIfnone)) {
    items.push_back(ParseIfnonePathDecl());
    return;
  }
  // Conditional path: if (...) (path)
  if (Check(TokenKind::kKwIf)) {
    Consume();
    Expect(TokenKind::kLParen);
    auto* cond = ParseExpr();
    Expect(TokenKind::kRParen);
    items.push_back(ParseConditionalPathDecl(cond));
    return;
  }
  // Simple path declaration: ( ... => ... ) = delay ;
  if (Check(TokenKind::kLParen)) {
    items.push_back(ParseSpecifyPathDecl());
    return;
  }
  // Unknown token inside specify - skip to avoid infinite loop.
  Consume();
}

// A.7.5.3: Parse a single edge_descriptor inside edge [ ... ].
// edge_descriptor ::= 01 | 10 | z_or_x zero_or_one | zero_or_one z_or_x
static bool IsZorX(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z';
}

static bool IsZeroOrOne(char c) { return c == '0' || c == '1'; }

// Parse edge qualifier: posedge | negedge | edge [ [...] ] | (nothing)
// A.7.5.3: edge_control_specifier ::= edge [ edge_descriptor { ,
// edge_descriptor } ]
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
    // A.7.5.3: Optional edge_control_specifier bracket list.
    if (edge_descriptors && Match(TokenKind::kLBracket)) {
      // Parse edge_descriptor { , edge_descriptor }
      do {
        auto text = CurrentToken().text;
        if (Check(TokenKind::kIntLiteral) && text.size() == 2 &&
            IsZeroOrOne(text[0]) && IsZeroOrOne(text[1])) {
          // 01 | 10 (or 00, 11 though unusual)
          edge_descriptors->push_back({text[0], text[1]});
          Consume();
        } else if (Check(TokenKind::kIdentifier) && text.size() == 2 &&
                   IsZorX(text[0]) && IsZeroOrOne(text[1])) {
          // z_or_x zero_or_one: x0, x1, z0, z1, X0, X1, Z0, Z1
          edge_descriptors->push_back({text[0], text[1]});
          Consume();
        } else if ((Check(TokenKind::kIntLiteral) && text.size() == 1 &&
                    IsZeroOrOne(text[0]))) {
          // zero_or_one z_or_x: 0x, 0z, 1x, 1z (two tokens)
          char first = text[0];
          Consume();
          auto next_text = CurrentToken().text;
          if (Check(TokenKind::kIdentifier) && next_text.size() == 1 &&
              IsZorX(next_text[0])) {
            edge_descriptors->push_back({first, next_text[0]});
            Consume();
          }
        } else {
          // Unknown token — skip to avoid infinite loop.
          Consume();
        }
      } while (Match(TokenKind::kComma));
      Expect(TokenKind::kRBracket);
    }
    return SpecifyEdge::kEdge;
  }
  return SpecifyEdge::kNone;
}

// Parse a single specify terminal: identifier [ . identifier ] [ [ range ] ]
SpecifyTerminal Parser::ParseSpecifyTerminal() {
  SpecifyTerminal term;
  term.name = Expect(TokenKind::kIdentifier).text;

  // Check for dotted interface.port form
  if (Match(TokenKind::kDot)) {
    term.interface_name = term.name;
    term.name = Expect(TokenKind::kIdentifier).text;
  }

  // Optional [ constant_range_expression ]
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
    Expect(TokenKind::kRBracket);
  }

  return term;
}

// Parse port list inside path: terminal {, terminal}
void Parser::ParsePathPorts(std::vector<SpecifyTerminal>& ports) {
  ports.push_back(ParseSpecifyTerminal());
  while (Match(TokenKind::kComma)) {
    ports.push_back(ParseSpecifyTerminal());
  }
}

// Parse delay values: mintypmax_expr or (mintypmax_expr, ...) after '='
// A.7.4: path_delay_value uses constant_mintypmax_expression
void Parser::ParsePathDelays(std::vector<Expr*>& delays) {
  auto loc = CurrentLoc();
  if (Match(TokenKind::kLParen)) {
    delays.push_back(ParseMinTypMaxExpr());
    while (Match(TokenKind::kComma)) {
      delays.push_back(ParseMinTypMaxExpr());
    }
    Expect(TokenKind::kRParen);
  } else {
    delays.push_back(ParseMinTypMaxExpr());
  }
  // A.7.4: list_of_path_delay_expressions allows exactly 1, 2, 3, 6, or 12
  auto n = delays.size();
  if (n != 1 && n != 2 && n != 3 && n != 6 && n != 12) {
    diag_.Error(loc, "path delay must have 1, 2, 3, 6, or 12 values");
  }
}

// Parse optional polarity operator: + | -
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

// Parse: ( [edge] src_ports [polarity] =>|*> dst_ports ) = delay ;
// Also handles edge-sensitive form: ( [edge] src [polarity] => ( dst [polarity]
// : data_source ) )
SpecifyItem* Parser::ParseSpecifyPathDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPathDecl;
  item->loc = CurrentLoc();

  Expect(TokenKind::kLParen);
  item->path.edge = ParseSpecifyEdge();
  ParsePathPorts(item->path.src_ports);

  // Optional polarity operator before => or *>
  item->path.polarity = ParseSpecifyPolarity();

  // => (parallel) or *> (full)
  // Handle +=> lexed as += then > (kPlusEq kGt)
  if (Match(TokenKind::kEqGt)) {
    item->path.path_kind = SpecifyPathKind::kParallel;
  } else if (Match(TokenKind::kStarGt)) {
    item->path.path_kind = SpecifyPathKind::kFull;
  } else if (item->path.polarity != SpecifyPolarity::kNone &&
             Match(TokenKind::kGt)) {
    // Polarity consumed a combined +=|-> token; kGt completes =>
    item->path.path_kind = SpecifyPathKind::kParallel;
  } else {
    // Try to recover
    Consume();
  }

  // Check for edge-sensitive data_source form: ( dst [polarity] : data_source )
  if (Match(TokenKind::kLParen)) {
    ParsePathPorts(item->path.dst_ports);
    item->path.dst_polarity = ParseSpecifyPolarity();
    Expect(TokenKind::kColon);
    item->path.data_source = ParseExpr();
    Expect(TokenKind::kRParen);
  } else {
    ParsePathPorts(item->path.dst_ports);
  }

  Expect(TokenKind::kRParen);
  Expect(TokenKind::kEq);
  ParsePathDelays(item->path.delays);
  Expect(TokenKind::kSemicolon);
  return item;
}

// Parse: if (cond) ( path ) = delay ;
SpecifyItem* Parser::ParseConditionalPathDecl(Expr* cond) {
  auto* item = ParseSpecifyPathDecl();
  item->path.condition = cond;
  return item;
}

// Parse: ifnone ( path ) = delay ;
SpecifyItem* Parser::ParseIfnonePathDecl() {
  Expect(TokenKind::kKwIfnone);
  auto* item = ParseSpecifyPathDecl();
  item->path.is_ifnone = true;
  return item;
}

// Map system identifier name to TimingCheckKind.
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

// Checks that require a data signal (two reference signals).
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

// Peek at the token after the current one and check if it's ',' or ')'.
bool Parser::CheckNextIsCommaOrRParen() {
  auto saved = lexer_.SavePos();
  Consume();  // Skip current token.
  bool result = Check(TokenKind::kComma) || Check(TokenKind::kRParen);
  lexer_.RestorePos(saved);
  return result;
}

// Parse additional limits and optional notifier after the first timing limit.
void Parser::ParseTimingCheckTrailingArgs(TimingCheckDecl& tc) {
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kRParen)) break;
    if (Check(TokenKind::kIdentifier) && CheckNextIsCommaOrRParen()) {
      tc.notifier = Consume().text;
      ParseExtendedTimingCheckArgs(tc);
      break;
    }
    tc.limits.push_back(ParseMinTypMaxExpr());
  }
}

// Parse extended args after notifier, dispatching by check kind.
void Parser::ParseExtendedTimingCheckArgs(TimingCheckDecl& tc) {
  // §31.8: $timeskew/$fullskew: event_based_flag, remain_active_flag.
  if (tc.check_kind == TimingCheckKind::kTimeskew ||
      tc.check_kind == TimingCheckKind::kFullskew) {
    // event_based_flag (expression or empty)
    if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
    if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
      tc.event_based_flag = ParseExpr();
    }
    // A.7.5.2: remain_active_flag ::= constant_mintypmax_expression
    if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
    if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
      tc.remain_active_flag = ParseMinTypMaxExpr();
    }
    return;
  }
  // §31.9: $setuphold/$recrem: timestamp_cond, timecheck_cond,
  // delayed_reference, delayed_data.
  // A.7.5.2: timestamp_condition ::= mintypmax_expression
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timestamp_cond = ParseMinTypMaxExpr();
  }
  // A.7.5.2: timecheck_condition ::= mintypmax_expression
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timecheck_cond = ParseMinTypMaxExpr();
  }
  // A.7.5.2: delayed_reference ::= terminal_identifier
  //          | terminal_identifier [ constant_mintypmax_expression ]
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (Check(TokenKind::kIdentifier)) {
    tc.delayed_ref = Consume().text;
    if (Match(TokenKind::kLBracket)) {
      tc.delayed_ref_expr = ParseMinTypMaxExpr();
      Expect(TokenKind::kRBracket);
    }
  }
  // A.7.5.2: delayed_data ::= terminal_identifier
  //          | terminal_identifier [ constant_mintypmax_expression ]
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (Check(TokenKind::kIdentifier)) {
    tc.delayed_data = Consume().text;
    if (Match(TokenKind::kLBracket)) {
      tc.delayed_data_expr = ParseMinTypMaxExpr();
      Expect(TokenKind::kRBracket);
    }
  }
}

// Parse: $setup(data [&&& cond], posedge clk [&&& cond], limit ...) ;
// A.7.5.3: timing_check_event uses specify_terminal_descriptor, not bare
// identifier.
SpecifyItem* Parser::ParseTimingCheck() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kTimingCheck;
  item->loc = CurrentLoc();

  auto name = CurrentToken().text;
  item->timing_check.check_kind = ParseTimingCheckKind(name);
  Consume();  // system identifier

  Expect(TokenKind::kLParen);

  // First signal argument (with optional edge and §31.7 condition).
  // A.7.5.3: timing_check_event ::=
  //   [ timing_check_event_control ] specify_terminal_descriptor
  //   [ &&& timing_check_condition ]
  item->timing_check.ref_edge =
      ParseSpecifyEdge(&item->timing_check.ref_edge_descriptors);
  item->timing_check.ref_terminal = ParseSpecifyTerminal();
  if (Match(TokenKind::kAmpAmpAmp)) {
    item->timing_check.ref_condition = ParseExpr();
  }
  Expect(TokenKind::kComma);

  // Second signal argument (with optional edge/condition) or limit.
  bool has_data_signal = NeedsDataSignal(item->timing_check.check_kind);
  if (has_data_signal) {
    item->timing_check.data_edge =
        ParseSpecifyEdge(&item->timing_check.data_edge_descriptors);
    item->timing_check.data_terminal = ParseSpecifyTerminal();
    if (Match(TokenKind::kAmpAmpAmp)) {
      item->timing_check.data_condition = ParseExpr();
    }
    Expect(TokenKind::kComma);
  }

  // Timing limit(s) and optional notifier / §31.9 extended args.
  // A.7.5.2: timing_check_limit ::= expression; but start_edge_offset and
  // end_edge_offset ($nochange) are mintypmax_expression. Using
  // ParseMinTypMaxExpr() handles both forms uniformly.
  item->timing_check.limits.push_back(ParseMinTypMaxExpr());
  ParseTimingCheckTrailingArgs(item->timing_check);
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return item;
}

// Parse: pulsestyle_onevent signal_list ;
// Parse: pulsestyle_ondetect signal_list ;
SpecifyItem* Parser::ParsePulsestyleDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPulsestyle;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwPulsestyleOndetect)) {
    item->is_ondetect = true;
  }
  Consume();  // pulsestyle keyword

  // Signal list
  item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

// Parse: showcancelled signal_list ;
// Parse: noshowcancelled signal_list ;
SpecifyItem* Parser::ParseShowcancelledDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kShowcancelled;
  item->loc = CurrentLoc();

  if (Check(TokenKind::kKwNoshowcancelled)) {
    item->is_noshowcancelled = true;
  }
  Consume();  // showcancelled/noshowcancelled keyword

  item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

// Parse: specparam name = expr ;  (inside specify block)
SpecifyItem* Parser::ParseSpecparamInSpecify() {
  auto* first = arena_.Create<SpecifyItem>();
  first->kind = SpecifyItemKind::kSpecparam;
  first->loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam);

  // Optional packed dimension [msb:lsb] (A.2.1.1)
  if (Check(TokenKind::kLBracket)) {
    Consume();
    ParseExpr();
    Expect(TokenKind::kColon);
    ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  // list_of_specparam_assignments (A.2.4)
  first->param_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kEq);
  // pulse_control_specparam: PATHPULSE$ = ( reject [, error] ) (A.2.4)
  if (first->param_name.starts_with("PATHPULSE$")) {
    Expect(TokenKind::kLParen);
    first->param_value = ParseMinTypMaxExpr();
    if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
    Expect(TokenKind::kRParen);
  } else {
    first->param_value = ParseMinTypMaxExpr();
  }
  while (Match(TokenKind::kComma)) {
    auto name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kEq);
    if (name.starts_with("PATHPULSE$")) {
      Expect(TokenKind::kLParen);
      ParseMinTypMaxExpr();
      if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      ParseMinTypMaxExpr();
    }
  }
  Expect(TokenKind::kSemicolon);
  return first;
}

}  // namespace delta
