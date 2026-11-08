#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/time_resolve.h"

namespace delta {

namespace {
struct TimeScopeTargets {
  ModuleDecl* mod;
  CompilationUnit* cu;
  PackageDecl* pkg;
};

struct TimeunitDecl {
  bool is_unit;
  bool unit_is_step;
  TimeUnit tu;
  int mag;
  SourceLoc loc;
};

template <typename Scope>
void ApplyScopeTimeUnit(Scope* scope, bool is_unit, TimeUnit tu, int mag) {
  if (!scope) return;
  if (is_unit) {
    scope->time_unit = tu;
    scope->time_unit_magnitude = mag;
    scope->has_timeunit = true;
  } else {
    scope->time_prec = tu;
    scope->time_prec_magnitude = mag;
    scope->has_timeprecision = true;
  }
}

void ApplyCuTimeUnit(CompilationUnit* cu, bool is_unit, TimeUnit tu, int mag,
                     SourceLoc loc) {
  if (!cu) return;
  if (is_unit) {
    cu->cu_time_unit = tu;
    cu->cu_time_unit_magnitude = mag;
    cu->has_cu_timeunit = true;
    cu->cu_timeunit_loc = loc;
  } else {
    cu->cu_time_prec = tu;
    cu->cu_time_prec_magnitude = mag;
    cu->has_cu_timeprecision = true;
    cu->cu_timeprecision_loc = loc;
  }
}
}  // namespace

static void ApplyTimeUnit(const TimeScopeTargets& targets,
                          const TimeunitDecl& decl) {
  ApplyScopeTimeUnit(targets.mod, decl.is_unit, decl.tu, decl.mag);
  ApplyCuTimeUnit(targets.cu, decl.is_unit, decl.tu, decl.mag, decl.loc);
  ApplyScopeTimeUnit(targets.pkg, decl.is_unit, decl.tu, decl.mag);
}

static void ApplyTimePrecision(const TimeScopeTargets& targets,
                               const TimeunitDecl& decl, TimeUnit prec,
                               int mag) {
  ApplyScopeTimeUnit(targets.mod, false, prec, mag);
  ApplyCuTimeUnit(targets.cu, false, prec, mag, decl.loc);
  ApplyScopeTimeUnit(targets.pkg, false, prec, mag);
}

namespace {
void ParsePrecisionFromToken(DiagEngine& diag, Token prec_tok,
                             const TimeunitDecl& decl,
                             const TimeScopeTargets& targets) {
  TimeUnit prec = TimeUnit::kNs;
  int prec_mag = 1;
  if (!TryParseTimeMagnitudeAndUnit(prec_tok.text, prec_mag, prec)) {
    diag.Error(prec_tok.loc,
               "time literal must use magnitude 1, 10, or 100 and unit "
               "s/ms/us/ns/ps/fs",
               Subclause("3.14"));
  }

  if (!decl.unit_is_step && EffectiveTimeOrder(prec, prec_mag) >
                                EffectiveTimeOrder(decl.tu, decl.mag)) {
    diag.Error(prec_tok.loc,
               "time precision is less precise than the time unit",
               Subclause("3.14"));
  }
  ApplyTimePrecision(targets, decl, prec, prec_mag);
}
}  // namespace

void Parser::ParseTimeunitDecl(ModuleDecl* mod, CompilationUnit* cu,
                               PackageDecl* pkg) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  auto kw_tok = Consume();
  if (in_anonymous_program_) {
    diag_.Error(kw_tok.loc,
                "an anonymous program may contain only task, function, class, "
                "interface class, covergroup, and class constructor "
                "declarations",
                Subclause("A.1.11"));
  }
  auto tok = Consume();
  TimeUnit tu = TimeUnit::kNs;
  int mag = 1;
  bool unit_is_step =
      Check(TokenKind::kIdentifier) && CurrentToken().text == "step";
  TimeScopeTargets targets{mod, cu, pkg};
  if (unit_is_step) {
    diag_.Error(
        tok.loc,
        "step cannot be used to set or modify the time unit or precision",
        Subclause("3.14.3"));
    Consume();
  } else {
    if (!TryParseTimeMagnitudeAndUnit(tok.text, mag, tu)) {
      diag_.Error(tok.loc,
                  "time literal must use magnitude 1, 10, or 100 and unit "
                  "s/ms/us/ns/ps/fs",
                  Subclause("3.14"));
    }
    ApplyTimeUnit(targets,
                  TimeunitDecl{is_unit, unit_is_step, tu, mag, kw_tok.loc});
  }
  auto slash_loc = CurrentLoc();
  if (Match(TokenKind::kSlash)) {
    auto prec_tok = Consume();
    if (!is_unit) {
      diag_.Error(slash_loc,
                  "timeprecision takes one time literal; the slash form "
                  "belongs to timeunit alone",
                  Subclause("3.14.2.2"));
      Expect(TokenKind::kSemicolon, Subclause("3.14.2.2"));
      return;
    }
    bool prec_is_step =
        Check(TokenKind::kIdentifier) && CurrentToken().text == "step";
    if (prec_is_step) {
      diag_.Error(
          prec_tok.loc,
          "step cannot be used to set or modify the time unit or precision",
          Subclause("3.14.3"));
      Consume();
    } else {
      ParsePrecisionFromToken(
          diag_, prec_tok,
          TimeunitDecl{is_unit, unit_is_step, tu, mag, kw_tok.loc}, targets);
    }
  }
  Expect(TokenKind::kSemicolon, Subclause("3.14.2.2"));
}
}  // namespace delta
