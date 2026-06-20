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
  Expect(TokenKind::kKwSpecify);

  while (!Check(TokenKind::kKwEndspecify) && !AtEnd()) {
    ParseSpecifyItem(item->specify_items);
  }
  Expect(TokenKind::kKwEndspecify);
  return item;
}

void Parser::ParseSpecparamDecl(std::vector<ModuleItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam);

  Expr* packed_left = nullptr;
  Expr* packed_right = nullptr;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    packed_left = ParseExpr();
    Expect(TokenKind::kColon);
    packed_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  auto parse_one = [&]() {
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kSpecparam;
    item->loc = kw_loc;
    item->data_type.packed_dim_left = packed_left;
    item->data_type.packed_dim_right = packed_right;
    item->name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kEq);
    if (item->name.starts_with("PATHPULSE$")) {
      Expect(TokenKind::kLParen);
      item->init_expr = ParseMinTypMaxExpr();
      if (Match(TokenKind::kComma)) ParseMinTypMaxExpr();
      Expect(TokenKind::kRParen);
    } else {
      item->init_expr = ParseMinTypMaxExpr();
    }
    items.push_back(item);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseSpecifyItem(std::vector<SpecifyItem*>& items) {
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

  if (Check(TokenKind::kSystemIdentifier)) {
    auto name = CurrentToken().text;
    if (IsTimingCheckName(name)) {
      items.push_back(ParseTimingCheck());
      return;
    }
    diag_.Error(CurrentLoc(), "system task cannot appear in specify block");
    while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
           !Check(TokenKind::kKwEndspecify) &&
           !Check(TokenKind::kKwEndmodule)) {
      Consume();
    }
    if (Check(TokenKind::kSemicolon)) Consume();
    return;
  }

  if (Check(TokenKind::kKwIfnone)) {
    items.push_back(ParseIfnonePathDecl());
    return;
  }

  if (Check(TokenKind::kKwIf)) {
    Consume();
    Expect(TokenKind::kLParen);
    auto* cond = ParseExpr();
    Expect(TokenKind::kRParen);
    items.push_back(ParseConditionalPathDecl(cond));
    return;
  }

  if (Check(TokenKind::kLParen)) {
    items.push_back(ParseSpecifyPathDecl());
    return;
  }

  diag_.Error(CurrentLoc(), "unexpected token in specify block");
  while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
         !Check(TokenKind::kKwEndspecify) && !Check(TokenKind::kKwEndmodule)) {
    Consume();
  }
  if (Check(TokenKind::kSemicolon)) Consume();
}

static bool IsZorX(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z';
}

static bool IsZeroOrOne(char c) { return c == '0' || c == '1'; }

void Parser::ParseEdgeDescriptorList(
    std::vector<std::pair<char, char>>& descriptors) {
  auto list_loc = CurrentLoc();
  do {
    if (Check(TokenKind::kRBracket)) break;
    auto text = CurrentToken().text;
    auto tok_loc = CurrentLoc();

    if ((Check(TokenKind::kIntLiteral) || Check(TokenKind::kIdentifier)) &&
        text.size() == 2 &&
        ((IsZorX(text[0]) && IsZeroOrOne(text[1])) ||
         (IsZeroOrOne(text[0]) && IsZeroOrOne(text[1]) &&
          text[0] != text[1]))) {
      descriptors.push_back({text[0], text[1]});
      Consume();
    } else if (Check(TokenKind::kIntLiteral) && text.size() == 1 &&
               IsZeroOrOne(text[0])) {
      char first = text[0];
      Consume();
      auto next_text = CurrentToken().text;
      if (Check(TokenKind::kIdentifier) && next_text.size() == 1 &&
          IsZorX(next_text[0])) {
        descriptors.push_back({first, next_text[0]});
        Consume();
      } else {
        diag_.Error(tok_loc, "invalid edge_descriptor");
      }
    } else {
      diag_.Error(tok_loc, "invalid edge_descriptor");
      Consume();
    }
  } while (Match(TokenKind::kComma));
  if (descriptors.empty()) {
    diag_.Error(list_loc,
                "edge-control specifier requires at least one edge_descriptor");
  }
  if (descriptors.size() > 6) {
    diag_.Error(list_loc,
                "edge-control specifier accepts at most six edge_descriptors");
  }
  Expect(TokenKind::kRBracket);
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
  term.name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kDot)) {
    term.interface_name = term.name;
    term.name = Expect(TokenKind::kIdentifier).text;
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
    Expect(TokenKind::kRBracket);
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
      Expect(TokenKind::kLBrace);
      ports.push_back(ParseSpecifyTerminal());
      while (Match(TokenKind::kComma)) {
        ports.push_back(ParseSpecifyTerminal());
      }
      Expect(TokenKind::kRBrace);
      Expect(TokenKind::kRBrace);
      return;
    }

    ports.push_back(ParseSpecifyTerminal());
    while (Match(TokenKind::kComma)) {
      ports.push_back(ParseSpecifyTerminal());
    }
    Expect(TokenKind::kRBrace);
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
    Expect(TokenKind::kRParen);
  } else {
    delays.push_back(ParseMinTypMaxExpr());
  }

  auto n = delays.size();
  if (n != 1 && n != 2 && n != 3 && n != 6 && n != 12) {
    diag_.Error(loc, "path delay must have 1, 2, 3, 6, or 12 values");
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

SpecifyItem* Parser::ParseSpecifyPathDecl() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kPathDecl;
  item->loc = CurrentLoc();

  Expect(TokenKind::kLParen);
  item->path.edge = ParseSpecifyEdge();
  ParsePathPorts(item->path.src_ports);

  item->path.polarity = ParseSpecifyPolarity();

  bool polarity_eq_gt_handled = false;
  if (item->path.polarity == SpecifyPolarity::kNone &&
      (Check(TokenKind::kPlusEq) || Check(TokenKind::kMinusEq))) {
    auto saved = lexer_.SavePos();
    bool is_plus = Check(TokenKind::kPlusEq);
    Consume();
    if (Match(TokenKind::kGt)) {
      item->path.polarity =
          is_plus ? SpecifyPolarity::kPositive : SpecifyPolarity::kNegative;
      item->path.path_kind = SpecifyPathKind::kParallel;
      polarity_eq_gt_handled = true;
    } else {
      lexer_.RestorePos(saved);
    }
  }

  if (!polarity_eq_gt_handled) {
    if (Match(TokenKind::kEqGt)) {
      item->path.path_kind = SpecifyPathKind::kParallel;
    } else if (Match(TokenKind::kStarGt)) {
      item->path.path_kind = SpecifyPathKind::kFull;
    } else {
      Consume();
    }
  }

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

  // Every parallel ('=>') form — plain, edge-sensitive, or with a data-source
  // expression — is described with a single input and a single output terminal
  // descriptor. Only the full ('*>') forms accept terminal lists.
  if (item->path.path_kind == SpecifyPathKind::kParallel &&
      (item->path.src_ports.size() != 1 || item->path.dst_ports.size() != 1)) {
    diag_.Error(item->loc,
                "parallel path '=>' requires a single source and "
                "destination terminal");
  }

  return item;
}

SpecifyItem* Parser::ParseConditionalPathDecl(Expr* cond) {
  auto* item = ParseSpecifyPathDecl();
  item->path.condition = cond;
  return item;
}

SpecifyItem* Parser::ParseIfnonePathDecl() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwIfnone);
  auto* item = ParseSpecifyPathDecl();
  item->path.is_ifnone = true;

  if (item->path.edge != SpecifyEdge::kNone ||
      item->path.data_source != nullptr) {
    diag_.Error(loc, "ifnone requires a simple path declaration");
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

    bool width_needs_threshold =
        tc.check_kind == TimingCheckKind::kWidth && tc.limits.size() < 2;
    if (!width_needs_threshold && Check(TokenKind::kIdentifier) &&
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
    Expect(TokenKind::kRBracket);
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

SpecifyItem* Parser::ParseTimingCheck() {
  auto* item = arena_.Create<SpecifyItem>();
  item->kind = SpecifyItemKind::kTimingCheck;
  item->loc = CurrentLoc();

  auto name = CurrentToken().text;
  item->timing_check.check_kind = ParseTimingCheckKind(name);
  Consume();

  Expect(TokenKind::kLParen);

  item->timing_check.ref_edge =
      ParseSpecifyEdge(&item->timing_check.ref_edge_descriptors);
  item->timing_check.ref_terminal = ParseSpecifyTerminal();
  if (Match(TokenKind::kAmpAmpAmp)) {
    item->timing_check.ref_condition = ParseExpr();
  }
  Expect(TokenKind::kComma);

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

  item->timing_check.limits.push_back(ParseMinTypMaxExpr());
  ParseTimingCheckTrailingArgs(item->timing_check);

  if (item->timing_check.check_kind == TimingCheckKind::kSetuphold &&
      item->timing_check.limits.size() < 2) {
    diag_.Error(item->loc,
                "$setuphold requires two timing_check_limit arguments");
  }

  if (item->timing_check.check_kind == TimingCheckKind::kRecrem &&
      item->timing_check.limits.size() < 2) {
    diag_.Error(item->loc, "$recrem requires two timing_check_limit arguments");
  }

  if (item->timing_check.check_kind == TimingCheckKind::kFullskew &&
      item->timing_check.limits.size() < 2) {
    diag_.Error(item->loc,
                "$fullskew requires two timing_check_limit arguments");
  }

  if (item->timing_check.check_kind == TimingCheckKind::kWidth &&
      item->timing_check.ref_edge == SpecifyEdge::kNone) {
    diag_.Error(item->loc,
                "$width reference_event must be an edge specification");
  }

  if (item->timing_check.check_kind == TimingCheckKind::kPeriod &&
      item->timing_check.ref_edge == SpecifyEdge::kNone) {
    diag_.Error(item->loc,
                "$period reference_event must be an edge specification");
  }

  if (item->timing_check.check_kind == TimingCheckKind::kNochange) {
    if (item->timing_check.limits.size() < 2) {
      diag_.Error(item->loc,
                  "$nochange requires both start_edge_offset and "
                  "end_edge_offset arguments");
    }
    if (item->timing_check.ref_edge != SpecifyEdge::kPosedge &&
        item->timing_check.ref_edge != SpecifyEdge::kNegedge) {
      diag_.Error(item->loc,
                  "$nochange reference_event must use posedge or negedge "
                  "(edge-control specifiers are not allowed)");
    }
  }
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
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

  item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kSemicolon);
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

  item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  while (Match(TokenKind::kComma)) {
    item->signal_list.push_back(Expect(TokenKind::kIdentifier).text);
  }
  Expect(TokenKind::kSemicolon);
  return item;
}

void Parser::ParseSpecparamInSpecify(std::vector<SpecifyItem*>& items) {
  auto kw_loc = CurrentLoc();
  Expect(TokenKind::kKwSpecparam);

  if (Check(TokenKind::kLBracket)) {
    Consume();
    ParseExpr();
    Expect(TokenKind::kColon);
    ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  auto parse_one = [&]() {
    auto* sp = arena_.Create<SpecifyItem>();
    sp->kind = SpecifyItemKind::kSpecparam;
    sp->loc = kw_loc;
    sp->param_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kEq);
    if (sp->param_name.starts_with("PATHPULSE$")) {
      sp->is_pathpulse = true;
      constexpr std::string_view kPrefix = "PATHPULSE$";
      std::string_view rest = sp->param_name.substr(kPrefix.size());
      if (!rest.empty()) {
        auto sep = rest.find('$');
        if (sep == std::string_view::npos) {
          sp->pathpulse_input = rest;
        } else {
          sp->pathpulse_input = rest.substr(0, sep);
          sp->pathpulse_output = rest.substr(sep + 1);
        }
      }
      Expect(TokenKind::kLParen);
      sp->pathpulse_reject = ParseMinTypMaxExpr();
      sp->param_value = sp->pathpulse_reject;
      if (Match(TokenKind::kComma)) {
        sp->pathpulse_error = ParseMinTypMaxExpr();
      }
      Expect(TokenKind::kRParen);
    } else {
      sp->param_value = ParseMinTypMaxExpr();
    }
    items.push_back(sp);
  };

  parse_one();
  while (Match(TokenKind::kComma)) parse_one();
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
