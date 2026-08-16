#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "preprocessor/preprocessor.h"

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;

  // Applied to the Elaborator that each entry point below builds, after it is
  // constructed and before it elaborates. Every entry point owns its
  // Elaborator as a local of the call, so a case that has to change a setting
  // on it has no other way to reach it. Left empty, nothing is applied and
  // each entry point behaves exactly as before.
  std::function<void(Elaborator&)> configure;
};

// Parses `src` and elaborates whatever the parser produced, reporting through
// `parse_failed` whether the parser added an error of its own before handing
// the compilation unit over. The two entry points below differ only in what
// they do with that answer.
//
// The count is read before and after rather than through DiagEngine::HasErrors,
// because a case may hand one fixture more than one source, and after the first
// rejection HasErrors answers for the whole engine rather than for this parse.
inline RtlirDesign* ElaborateSrcReportingParse(const std::string& src,
                                               ElabFixture& f,
                                               std::string_view top,
                                               bool& parse_failed) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  uint32_t errors_before_parse = f.diag.ErrorCount();
  auto* cu = parser.Parse();
  parse_failed = f.diag.ErrorCount() != errors_before_parse;
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  // With no explicit top and no top-level module (empty/whitespace/comment-only
  // or package/class-only source), pass an empty name; the elaborator validates
  // and elaborates the compilation unit as-is rather than dereferencing an
  // empty module list (which was undefined behavior, crashing on arm64).
  std::string_view name = top;
  if (name.empty() && !cu->modules.empty()) name = cu->modules.back()->name;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// Elaborates `src`, and fails the case when `src` did not parse.
//
// A case that hands over a source the parser rejects is asking about
// elaboration and has been given a fragment to ask about, so whatever it
// asserts next is vacuous. A case asserting a rejection is the one this costs:
// a misspelling or a reserved word used as an identifier produces the same
// errors the rule would, so the case passes for as long as it stands and it is
// the case covering the rule. ElabOk has asked this since it was written; the
// wording here follows it.
//
// The failure does not stop the elaboration. ElabOk answers a bool and has
// somewhere to return to, while callers here dereference the design, so the
// report is raised and the run carries on exactly as before. Nothing that
// passes today changes behaviour; a case that was passing on a syntax error
// gains a failure naming its own input.
//
// A case that means to drive a parser diagnostic through this fixture calls
// ElaborateSrcAllowingParseErrors below, which records that intent where a
// reader will find it.
inline RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f,
                                 std::string_view top = "") {
  bool parse_failed = false;
  auto* design = ElaborateSrcReportingParse(src, f, top, parse_failed);
  if (parse_failed) {
    ADD_FAILURE() << "the source did not parse, so nothing but a fragment was "
                     "elaborated and every answer about elaboration is "
                     "vacuous:\n"
                  << src;
  }
  return design;
}

// Elaborates `src` without asking whether it parsed, for a case whose subject
// is the parser's own report and which reaches it through this fixture. The
// name is the record of that intent: an argument saying the same thing would
// leave the reason at the call site unstated.
inline RtlirDesign* ElaborateSrcAllowingParseErrors(const std::string& src,
                                                    ElabFixture& f,
                                                    std::string_view top = "") {
  bool parse_failed = false;
  return ElaborateSrcReportingParse(src, f, top, parse_failed);
}

inline RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                              std::string_view top = "") {
  return ElaborateSrc(src, f, top);
}

// Runs the preprocess -> parse prologue on an already-registered source file
// and returns the resulting CompilationUnit. The caller owns `preproc` so that
// it can read back preprocessor state after parsing.
inline CompilationUnit* PreprocessAndParseCu(ElabFixture& f, uint32_t fid,
                                             Preprocessor& preproc) {
  auto pp = preproc.Preprocess(fid);
  // Registered with its origins, as the AddPreprocessedFile call in
  // ParseSource in src/main.cpp registers it, so a report this fixture
  // provokes is formatted the way the binary formats it.
  auto pp_fid =
      f.mgr.AddPreprocessedFile("<preprocessed>", pp, preproc.LineOrigins());
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

// Propagates the decay-time, trireg-strength, and delay-mode directives from
// the preprocessor onto the CompilationUnit.
inline void PropagateDecayAndDelayToCu(CompilationUnit* cu,
                                       Preprocessor& preproc) {
  cu->default_decay_time = preproc.DefaultDecayTime();
  cu->default_decay_time_real = preproc.DefaultDecayTimeReal();
  cu->default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  cu->default_trireg_strength = preproc.DefaultTriregStrength();
  cu->has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  cu->delay_mode_directive = preproc.DelayModeDirective();
}

// Preprocesses, parses and elaborates `src`, reporting through `parse_failed`
// whether the preprocessor or the parser added an error of its own before the
// compilation unit was handed over. The two entry points below differ only in
// what they do with that answer.
//
// A misspelled directive is counted here as a rejection like any other. It is
// reported by the preprocessor rather than the parser, and it leaves the same
// fragment behind, so a case whose define directive never took effect is asking
// about elaboration and has been given something else to ask about.
//
// The count is read before and after for the reason ElaborateSrcReportingParse
// records: a case may hand one fixture more than one source.
//
// When `auto_top` is set, no top module is named and the elaborator roots every
// uninstantiated module as a top (§23.3.1) rather than the single last module;
// used by tests that check multi-top designs.
inline RtlirDesign* ElaborateWithPreprocessorReportingParse(
    const std::string& src, ElabFixture& f, std::string_view top, bool auto_top,
    bool& parse_failed) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  uint32_t errors_before_parse = f.diag.ErrorCount();
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  parse_failed = f.diag.ErrorCount() != errors_before_parse;
  // Propagate preprocessor state to CompilationUnit.
  cu->default_nettype = preproc.DefaultNetType();
  cu->unconnected_drive = preproc.UnconnectedDrive();
  for (auto* mod : cu->modules) {
    for (const auto& cell_name : preproc.CellModuleNames()) {
      if (mod->name == cell_name) {
        mod->is_cell = true;
        break;
      }
    }
  }
  PropagateDecayAndDelayToCu(cu, preproc);
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  // See ElaborateSrc: with no explicit top and no top-level module, pass an
  // empty name instead of dereferencing an empty module list.
  std::string_view name = top;
  if (!auto_top && name.empty() && !cu->modules.empty())
    name = cu->modules.back()->name;
  auto* design = elab.Elaborate(name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// Elaborates `src` through the preprocessor, and fails the case when `src` did
// not get through the preprocessor and the parser.
//
// This is the same guard ElaborateSrc carries and it is here for the same
// reason: a case handed a fragment asserts about elaboration and is answered by
// the parser's errors, so it passes whether the rule it names exists or not.
// #3080 measured that on ElaborateSrc and found thirteen call sites in the
// state.
//
// The failure does not stop the elaboration, because callers dereference the
// design. A case that means to drive a preprocessor or parser diagnostic
// through this fixture calls ElaborateWithPreprocessorAllowingParseErrors.
inline RtlirDesign* ElaborateWithPreprocessor(const std::string& src,
                                              ElabFixture& f,
                                              std::string_view top = "",
                                              bool auto_top = false) {
  bool parse_failed = false;
  auto* design = ElaborateWithPreprocessorReportingParse(src, f, top, auto_top,
                                                         parse_failed);
  if (parse_failed) {
    ADD_FAILURE()
        << "the source did not preprocess and parse, so nothing but a "
           "fragment was elaborated and every answer about "
           "elaboration is vacuous:\n"
        << src;
  }
  return design;
}

// Elaborates `src` without asking whether it got through the preprocessor and
// the parser, for a case whose subject is one of their reports. The name is the
// record of that intent, as it is for ElaborateSrcAllowingParseErrors.
inline RtlirDesign* ElaborateWithPreprocessorAllowingParseErrors(
    const std::string& src, ElabFixture& f, std::string_view top = "",
    bool auto_top = false) {
  bool parse_failed = false;
  return ElaborateWithPreprocessorReportingParse(src, f, top, auto_top,
                                                 parse_failed);
}

// Answers whether the elaborator accepts `src`, which is a question about
// elaboration and presupposes that there is something to elaborate. A source
// the parser rejected never reaches the elaborator, so `false` would answer a
// question nobody asked -- and a case asserting that the elaborator rejects
// something would hold whatever the rule it names does, because a misspelling
// or a reserved word used as an identifier produces the same `false` the rule
// does. Such a case is reported as passing for as long as it stands, and it is
// the case covering the rule.
//
// So the source's own well-formedness is asserted here, where the source is
// handed over, rather than left to whatever the case checks afterwards. The
// failure then names the input.
//
// A source that parses and declares no module is a different shape and is not
// read here: `false` is a truthful answer to a case that handed over nothing
// to elaborate, and cases about packages and classes alone rely on it.
//
// The caller supplies the fixture, so the engine that recorded the diagnostics
// outlives the answer and a case that asserts a rejection can go on to name
// the diagnostic it was rejected with. The answer alone says only that the
// elaborator refused the source, which every cause of a refusal says equally.
inline bool ElabOk(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto* cu = PreprocessAndParseCu(f, fid, preproc);
  f.has_errors = f.diag.HasErrors();
  if (f.has_errors) {
    ADD_FAILURE() << "the source did not parse, so nothing was elaborated "
                     "and every answer about elaboration is vacuous:\n"
                  << src;
    return false;
  }
  if (cu->modules.empty()) return false;
  Elaborator elab(f.arena, f.diag, cu);
  if (f.configure) f.configure(elab);
  elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return !f.has_errors;
}

// The same question for a case that wants nothing but the answer. The fixture
// lives as long as the call and is gone once it returns, which is why a case
// reading the diagnostics back calls the form above instead.
inline bool ElabOk(const std::string& src) {
  ElabFixture f;
  return ElabOk(src, f);
}

// The first diagnostic the fixture's engine recorded whose message contains
// `needle`, or nullptr when it recorded none. A test that asserts which
// subclause of IEEE 1800-2023 a rejection enforced reads the subclause off
// this rather than off whichever report the run happened to write first: one
// source can be rejected for more than one reason, and the first report is
// then a different rule's. A null return says the source never provoked the
// report the test is about, which a count of errors cannot distinguish from
// provoking a different one.
inline const Diagnostic* FindDiag(const ElabFixture& f,
                                  std::string_view needle) {
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message.find(needle) != std::string::npos) return &diag;
  }
  return nullptr;
}
