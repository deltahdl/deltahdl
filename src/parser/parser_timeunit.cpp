// §3.14.2: the timeunit and timeprecision declarations, and what one of them
// updates.
//
// §3.14.2.1 gives a design element one time unit and one time precision, and
// §3.14.2.2 states where a declaration of either may stand and which scope it
// belongs to. A single declaration can reach an enclosing module, the
// compilation unit or an enclosing package, so what a parse of one has to
// produce is not a value but an update applied to whichever of those three the
// declaration was written in.
//
// This was the tail of src/parser/parser.cpp, which reached 975 lines against
// the 1000 assert-no-oversized-source-files in .github/workflows/deltahdl.yml
// fails at. Nothing here is reached from that file except through
// Parser::ParseTimeunitDecl, and everything here reaches back into it only
// through Parser members src/parser/parser.h declares.

#include <string_view>

#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "parser/time_resolve.h"

namespace delta {

namespace {
// The three SystemVerilog scopes (§3.14.2) whose timeunit/timeprecision a
// single "timeunit"/"timeprecision" declaration can update: an enclosing
// module, the compilation unit, and an enclosing package. Any subset may be
// null.
struct TimeScopeTargets {
  ModuleDecl* mod;
  CompilationUnit* cu;
  PackageDecl* pkg;
};

// The already-parsed "unit" part of a timeunit/timeprecision declaration
// (§3.14.2): whether it is a timeunit (vs timeprecision) declaration, whether
// the unit token was the literal 'step', and the parsed unit value.
struct TimeunitDecl {
  bool is_unit;
  bool unit_is_step;
  TimeUnit tu;
  int mag;
};

// Apply a timeunit/timeprecision setting to a single scope (module, package, or
// any type whose timeunit fields are named time_unit/time_prec). The
// compilation-unit scope uses differently named fields and is handled
// separately by ApplyCuTimeUnit.
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

void ApplyCuTimeUnit(CompilationUnit* cu, bool is_unit, TimeUnit tu, int mag) {
  if (!cu) return;
  if (is_unit) {
    cu->cu_time_unit = tu;
    cu->cu_time_unit_magnitude = mag;
    cu->has_cu_timeunit = true;
  } else {
    cu->cu_time_prec = tu;
    cu->cu_time_prec_magnitude = mag;
    cu->has_cu_timeprecision = true;
  }
}
}  // namespace

static void ApplyTimeUnit(const TimeScopeTargets& targets,
                          const TimeunitDecl& decl) {
  ApplyScopeTimeUnit(targets.mod, decl.is_unit, decl.tu, decl.mag);
  ApplyCuTimeUnit(targets.cu, decl.is_unit, decl.tu, decl.mag);
  ApplyScopeTimeUnit(targets.pkg, decl.is_unit, decl.tu, decl.mag);
}

static void ApplyTimePrecision(const TimeScopeTargets& targets, TimeUnit prec,
                               int mag) {
  if (targets.mod) {
    targets.mod->time_prec = prec;
    targets.mod->time_prec_magnitude = mag;
    targets.mod->has_timeprecision = true;
  }
  if (targets.cu) {
    targets.cu->cu_time_prec = prec;
    targets.cu->cu_time_prec_magnitude = mag;
    targets.cu->has_cu_timeprecision = true;
  }
  if (targets.pkg) {
    targets.pkg->time_prec = prec;
    targets.pkg->time_prec_magnitude = mag;
    targets.pkg->has_timeprecision = true;
  }
}

namespace {
// Validate the precision side of a "timeunit <unit> / <precision>" declaration
// (its token already consumed and known not to be 'step'), reporting a bad
// literal or a precision coarser than the unit, then store it when the
// declaration is a timeunit. Mirrors the inline logic it replaces exactly.
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
  if (decl.is_unit) ApplyTimePrecision(targets, prec, prec_mag);
}
}  // namespace

void Parser::ParseTimeunitDecl(ModuleDecl* mod, CompilationUnit* cu,
                               PackageDecl* pkg) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  Consume();
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
    ApplyTimeUnit(targets, TimeunitDecl{is_unit, unit_is_step, tu, mag});
  }
  if (Match(TokenKind::kSlash)) {
    auto prec_tok = Consume();
    bool prec_is_step =
        Check(TokenKind::kIdentifier) && CurrentToken().text == "step";
    if (prec_is_step) {
      diag_.Error(
          prec_tok.loc,
          "step cannot be used to set or modify the time unit or precision",
          Subclause("3.14.3"));
      Consume();
    } else {
      ParsePrecisionFromToken(diag_, prec_tok,
                              TimeunitDecl{is_unit, unit_is_step, tu, mag},
                              targets);
    }
  }
  Expect(TokenKind::kSemicolon, Subclause("3.14.2.2"));
}
}  // namespace delta
