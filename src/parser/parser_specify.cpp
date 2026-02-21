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

// Parse edge qualifier: posedge | negedge | edge | (nothing)
SpecifyEdge Parser::ParseSpecifyEdge() {
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
// Also handles edge-sensitive form: ( [edge] src [polarity] => ( dst [polarity] : data_source ) )
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
    tc.limits.push_back(ParseExpr());
  }
}

// §31.9: Parse extended args after notifier: timestamp_cond, timecheck_cond,
// delayed_reference, delayed_data.
void Parser::ParseExtendedTimingCheckArgs(TimingCheckDecl& tc) {
  // timestamp_condition (expression or empty)
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timestamp_cond = ParseExpr();
  }
  // timecheck_condition (expression or empty)
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen)) {
    tc.timecheck_cond = ParseExpr();
  }
  // delayed_reference (identifier or empty)
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (Check(TokenKind::kIdentifier)) {
    tc.delayed_ref = Consume().text;
  }
  // delayed_data (identifier or empty)
  if (!Match(TokenKind::kComma) || Check(TokenKind::kRParen)) return;
  if (Check(TokenKind::kIdentifier)) {
    tc.delayed_data = Consume().text;
  }
}

// Parse: $setup(data [&&& cond], posedge clk [&&& cond], limit ...) ;
SpecifyItem* Parser::ParseTimingCheck() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kTimingCheck;
  item->loc = CurrentLoc();

  auto name = CurrentToken().text;
  item->timing_check.check_kind = ParseTimingCheckKind(name);
  Consume();  // system identifier

  Expect(TokenKind::kLParen);

  // First signal argument (with optional edge and §31.7 condition).
  item->timing_check.ref_edge = ParseSpecifyEdge();
  item->timing_check.ref_signal = Expect(TokenKind::kIdentifier).text;
  if (Match(TokenKind::kAmpAmpAmp)) {
    item->timing_check.ref_condition = ParseExpr();
  }
  Expect(TokenKind::kComma);

  // Second signal argument (with optional edge/condition) or limit.
  bool has_data_signal = NeedsDataSignal(item->timing_check.check_kind);
  if (has_data_signal) {
    item->timing_check.data_edge = ParseSpecifyEdge();
    item->timing_check.data_signal = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kAmpAmpAmp)) {
      item->timing_check.data_condition = ParseExpr();
    }
    Expect(TokenKind::kComma);
  }

  // Timing limit(s) and optional notifier / §31.9 extended args.
  item->timing_check.limits.push_back(ParseExpr());
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
