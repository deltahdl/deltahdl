#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "helpers_protect_viewport.h"
#include "helpers_reported_error.h"

using namespace delta;

// §34.5.32.2 Description, for the viewport protect pragma keyword.
//
// Every other keyword of §34.5 seals a design away. This one asks for part of
// it back, and the subclause says so in three sentences.
//
//   The expression describes objects within the current protected envelope for
//   which access shall be permitted by the SystemVerilog tool. Table 34-1 puts
//   the same thing in five words: it modifies the scope of access into a
//   decryption envelope.
//
//   The specified object name shall be contained within the current envelope.
//
//   The access value is an implementation-specific relaxation of protection.
//
// The first sentence is what this file reads. A viewport is gathered for the
// envelope in force by Preprocessor::ApplyViewport in
// src/preprocessor/preprocessor_protect_viewport.cpp and read back through
// Preprocessor::ProtectViewports; the spelling it has to be written in is
// §34.5.32.1's, read by ParseProtectViewport in
// src/preprocessor/protect_viewport.cpp and covered in
// test_preprocessor_subclause_34_05_32_01.cpp rather than here.
//
// The second sentence is decided here only where no envelope is open at all,
// which is the one case a reading can settle without knowing what the envelope
// holds. Beyond that it is out of reach at this stage: the preprocessor has no
// symbol table, so nothing here can say whether a name is one of the objects
// the envelope contains. A decryption envelope's viewports are kept in the
// SourceManager where it closes, and the elaborator resolves and reports them
// (ReportViewportsContainingNothing in src/elaborator/viewport_resolution.cpp).
//
// The third sentence is this tool's to define, and the last section here is
// about the reading's part of it: an access value this tool does not define is
// reported as granting nothing, and the two it does define are not reported.

namespace {

// The object a source names and the access it asks for it. The object is
// written with more than one component, as a name of an item of a design
// element the envelope declares is, and the access holds characters no keyword
// is spelled with, so a value read back is the one the directive wrote.
constexpr std::string_view kObject = "dut.mem";
constexpr std::string_view kAccess = "read-only";

// A second object of the same envelope, for the case describing two.
constexpr std::string_view kOtherObject = "dut.ctrl";

// An access no part of the standard mentions. §34.5.32.2 leaves the value to
// the implementation, so a reading that admitted a fixed list of spellings
// would turn this away and one that carries what it was given will not.
constexpr std::string_view kOwnAccess = "x-meridian-scan";

// The two expressions that open an envelope. §34.5.3.1 spells the one a
// reading meets in a sealed model, and §34.5.1.1 the one an author writes
// around the cleartext being sealed. A viewport is written inside either, so
// both are read here.
constexpr std::string_view kOpensDecryption =
    "`pragma protect begin_protected\n";
constexpr std::string_view kOpensEncryption = "`pragma protect begin\n";

// The expression closing the first of those.
constexpr std::string_view kClosesDecryption =
    "`pragma protect end_protected\n";

// The message Preprocessor::ApplyViewport reports an expression standing in no
// envelope with.
constexpr std::string_view kNoEnvelope =
    "viewport expression stands in no protected envelope";

// The message Preprocessor::ApplyViewport answers a viewport asking for an
// access this tool does not define with. The fragment is the part naming the
// rule rather than the whole of it, which also quotes the value asked for.
constexpr std::string_view kGrantsNothing = "is not one this tool defines";

// ---------------------------------------------------------------------------
// The expression describes objects within the current protected envelope.
// ---------------------------------------------------------------------------

// A viewport inside an open decryption envelope describes an object of it, and
// the name comes back whole: §34.5.32.2 has the name specify an object
// contained within the envelope, and an item of a design element the envelope
// declares is named through that element, so a reading keeping the last
// component alone would describe a different object from the one asked for.
TEST(ProtectViewportDescription, ADecryptionEnvelopeIsDescribedByOneInside) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

// An author's own cleartext writes one too, inside the begin-end pair §34.5.1
// has it seal the design with. A reading that gathered a viewport only where a
// sealed model was being opened would take an author's own request for
// something else.
TEST(ProtectViewportDescription, AnEncryptionRegionIsDescribedByOneInside) {
  ReadingViewports reading(std::string(kOpensEncryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

// §34.5.32.2 has the expression describe objects, and one expression names one
// object. An envelope naming two is described by both, in the order the text
// named them: a reading keeping only the most recent writing of the keyword --
// which is what §34.4 does with a keyword's value -- would have the second
// alone.
TEST(ProtectViewportDescription, TwoObjectsAreDescribedInTheOrderWritten) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 2U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().back().object, kOtherObject);
}

// ---------------------------------------------------------------------------
// The specified object name shall be contained within the current envelope.
// ---------------------------------------------------------------------------

// Where no envelope is open there is no current envelope for an object to be
// contained within, whichever object the expression named, so the rule is
// broken by the position alone and the report says which rule it was.
TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeIsReported) {
  ReadingViewports reading(ViewportOf(kObject, kAccess));
  EXPECT_TRUE(
      ReportedError(reading.diag.Diagnostics(), kNoEnvelope, 1, "34.5.32.2"));
}

// The other half of that: nothing is described either. Without this the two
// cases above would hold of a reading that gathered every viewport it met and
// merely complained about some of them.
TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeDescribesNothing) {
  ReadingViewports reading(ViewportOf(kObject, kAccess));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

// ---------------------------------------------------------------------------
// The envelope the description belongs to.
// ---------------------------------------------------------------------------

// The objects are the current envelope's, so they end where it does. A reading
// that carried them past the closing expression would offer one envelope's
// relaxation to whatever the compilation input held next.
TEST(ProtectViewportDescription, TheDescriptionEndsWithTheEnvelopeItWasIn) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           std::string(kClosesDecryption));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

// And an envelope opening inside one is a different current envelope, which no
// object of the envelope around it has been described within. This is the case
// the one above cannot make: after a closing expression there is no envelope
// at all, so a reading that simply dropped everything at the end of the input
// would satisfy it.
TEST(ProtectViewportDescription, AnEnvelopeOpeningInsideOneDescribesNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           std::string(kOpensDecryption));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

// A viewport written after the inner envelope opened belongs to that one, so
// the description an envelope carries is its own rather than the last one the
// reading saw anywhere. Without this the case above would hold of a reading
// that had stopped gathering viewports altogether.
TEST(ProtectViewportDescription, TheInnerEnvelopeIsDescribedByItsOwn) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kOtherObject);
}

// §34.5.31.2 restores every protect pragma keyword to its default, and what an
// envelope has been described by is not one of those values: it is a request
// the envelope already made, as §34.5.30.2's comment is an output already owed
// where a reset follows it. So the description an envelope carries survives a
// reset written inside that envelope, and only the envelope ending takes it.
//
// The keyword's own value does go back, and the two are different things. What
// a directive wrote against the name is held in ProtectKeywordScope
// (src/preprocessor/protect_keywords.h), which ProtectKeywordScope::Reset
// clears, so after this reset ProtectKeywords().ValueOf(kViewportKeyword)
// reports the keyword defaulted while the objects below still stand. That is
// not two answers to one question: the first says what value is in effect for
// the keyword from here on, and the second says which objects the envelope has
// been asked to permit access to. #3444 was filed calling the difference a
// defect and closed on this case, so a reading that takes the two for one
// thing has been tried.
TEST(ProtectViewportDescription, AResetLeavesWhatTheEnvelopeWasDescribedBy) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           "`pragma protect reset\n");
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

// ---------------------------------------------------------------------------
// The access value is an implementation-specific relaxation of protection.
// ---------------------------------------------------------------------------

// The value is carried as the directive wrote it, which is what a tool that
// went on to relax anything would have to work from.
TEST(ProtectViewportDescription, TheAccessIsCarriedAsWritten) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

// §34.5.32.2 leaves the value to the implementation, so no spelling of it is
// better than another and none is turned away. A value the standard never
// mentions is carried exactly as the one above is, which is what makes that
// case about carrying the value rather than about recognizing it.
TEST(ProtectViewportDescription, AnAccessTheStandardNeverNamesIsCarriedToo) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kOwnAccess);
}

// ---------------------------------------------------------------------------
// The access values this implementation defines.
// ---------------------------------------------------------------------------

// This tool defines two access values, "r" and "rw" (ViewportAccessOf in
// src/common/envelope_viewport.h, listed in README.md), and a viewport asking
// for either is granted it where the design's objects are attached, so the
// reading has nothing to say about it.
TEST(ProtectViewportDescription, AReadAccessDrawsNoReport) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, "r"));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

// The second of the two.
TEST(ProtectViewportDescription, AReadWriteAccessDrawsNoReport) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, "rw"));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

// Any other value relaxes nothing, and a text that asked for it is told so at
// the viewport rather than left to assume it was granted. It is a warning
// because the expression breaks no rule of §34.5.32: the value is left to the
// implementation, and what goes unanswered is the grant rather than the
// writing.
TEST(ProtectViewportDescription, AnUndefinedAccessIsReportedAsGrantingNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 2,
                              "34.5.32.2"));
}

// The other half of the report's severity: the expression is accepted. The
// viewport is gathered and no error stands against the text, so a producer's
// model still compiles.
TEST(ProtectViewportDescription, TheReportLeavesTheViewportGathered) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

// A protected envelope that asked for nothing is told nothing. The envelope
// here carries a content keyword of its own, so the case says the report
// follows the viewport rather than the protect pragma directive standing
// inside an envelope.
TEST(ProtectViewportDescription, AnEnvelopeAskingForNoAccessIsToldNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ProtectDirective("author = \"acme\""));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

// §34.5.32.2 has each expression describe its own object, so each one asking
// for an access this tool does not define is answered at its own line.
TEST(ProtectViewportDescription, EachUndefinedAccessIsReportedAtItsOwnLine) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           ViewportOf(kOtherObject, kOwnAccess));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 2,
                              "34.5.32.2"));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 3,
                              "34.5.32.2"));
}

// An expression standing in no envelope is reported under §34.5.32.2 and stops
// there, the object it named being contained in nothing. So the two reports
// are alternatives rather than a pair: a text told its viewport describes no
// envelope is not also told what its access would have granted.
TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeIsNotAnsweredTwice) {
  ReadingViewports reading(ViewportOf(kObject, kOwnAccess));
  EXPECT_FALSE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 1,
                               "34.5.32.2"));
}

// §34.2 permits the nesting -- "Decryption envelopes may contain other
// envelopes within their enclosed data block" -- and §34.5.32.2 gives a
// viewport to "the current protected envelope", so which envelope is current
// changes as one opens inside another and the outer is current again when the
// inner has closed. It is still described by what it wrote.
//
// The viewports were held in one flat list cleared at every envelope boundary,
// so the inner envelope's opening wiped the outer's before its closing could,
// and the outer envelope came back described by nothing. A single envelope
// cannot fail this: one open and one close leave nothing to lose.
TEST(ProtectViewportDescription, AnInnerEnvelopeDoesNotWipeTheOuters) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + std::string(kClosesDecryption));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

// The inner envelope is described by its own and by nothing of the outer's,
// which is the other half of "the current protected envelope": while the inner
// stands it is current, and the outer's viewport describes an object of the
// outer.
TEST(ProtectViewportDescription, AnInnerEnvelopeIsDescribedByItsOwnAlone) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kOtherObject);
}

// And the outer's own comes back when the inner closes, beside the one it had
// before -- so what returns is the outer envelope's list rather than an empty
// one that the outer then refills.
TEST(ProtectViewportDescription, TheOutersViewportsReturnWhenTheInnerCloses) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess) +
      std::string(kClosesDecryption));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

}  // namespace
