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
// the unit token was the literal 'step', the parsed unit value, and where the
// declaration's leading keyword stands. The position is carried because
// §3.14.2.2 requires a repeat to "match the previous declaration within the
// current time scope" and a report about a repeat has to stand at it; the
// compilation-unit scope keeps it, since that scope outlives the parse that
// wrote it.
struct TimeunitDecl {
  bool is_unit;
  bool unit_is_step;
  TimeUnit tu;
  int mag;
  SourceLoc loc;
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

// `loc` is stored beside whichever flag this sets, and is the position of the
// declaration's leading timeunit/timeprecision keyword. A module or a package
// keeps no such position because its scope is one file's, so a repeat that does
// not match it is reported by ValidateTimeScopeAfterParse in
// src/parser/parser_items.cpp while that file is still being parsed. The
// compilation-unit scope spans a whole command line (§3.12.1 case a)), so its
// position has to outlive the parse.
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

// The precision named after the slash of "timeunit <unit> / <precision>"
// (§3.14.2.2: "The time precision may also be declared using an optional second
// argument to the timeunit keyword using the slash separator"). `decl` is the
// declaration the slash belongs to, read for its position alone: the precision
// is declared by the same statement as the unit, so a report about it stands
// where CheckCuTimeunitConsistency in src/parser/parser.cpp stands, at the
// leading keyword rather than at the token after the slash.
static void ApplyTimePrecision(const TimeScopeTargets& targets,
                               const TimeunitDecl& decl, TimeUnit prec,
                               int mag) {
  ApplyScopeTimeUnit(targets.mod, /*is_unit=*/false, prec, mag);
  ApplyCuTimeUnit(targets.cu, /*is_unit=*/false, prec, mag, decl.loc);
  ApplyScopeTimeUnit(targets.pkg, /*is_unit=*/false, prec, mag);
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
  if (decl.is_unit) ApplyTimePrecision(targets, decl, prec, prec_mag);
}
}  // namespace

void Parser::ParseTimeunitDecl(ModuleDecl* mod, CompilationUnit* cu,
                               PackageDecl* pkg) {
  bool is_unit = Check(TokenKind::kKwTimeunit);
  // The leading timeunit/timeprecision keyword, kept because it is where a
  // report about this declaration stands: the caller in src/parser/parser.cpp
  // that hands CheckCuTimeunitConsistency a position reads CurrentLoc() here,
  // before this function is entered, so recording the same token is what makes
  // the cross-file report of §3.14.2.2 land where the within-file one does.
  auto kw_tok = Consume();
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
      ParsePrecisionFromToken(
          diag_, prec_tok,
          TimeunitDecl{is_unit, unit_is_step, tu, mag, kw_tok.loc}, targets);
    }
  }
  Expect(TokenKind::kSemicolon, Subclause("3.14.2.2"));
}
}  // namespace delta
