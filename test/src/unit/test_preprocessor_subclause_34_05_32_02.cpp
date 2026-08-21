#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_viewport.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_viewport.h"

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
// holds. Beyond that it is out of reach at this stage and is left so
// deliberately: the preprocessor has no symbol table and never parses the
// cleartext a data block recovers -- Preprocessor::DecryptDataBlock in
// src/preprocessor/preprocessor_protect_keys.cpp appends that text to the
// output and keeps no name out of it -- so nothing here can say whether
// top.dut.mem is one of the objects the envelope contains. The phase that
// resolves such a name is the elaborator, where HierPath in
// src/elaborator/rtlir.h and Elaborator::CheckHierRefUndeclaredMember in
// src/elaborator/elaborator_scope_rules_hier.cpp already do it.
//
// The third sentence is performed by nothing. No access is permitted to
// anything, because nothing downstream of the preprocessor is told a design
// element came out of a protected envelope, so there is no protection of an
// object for a relaxation to relax. What this file holds the value to is
// therefore only that it is carried as written and that no spelling of it is
// judged, which is what "implementation-specific" leaves open. #3284 records
// both gaps.

namespace {

// The object a source names and the access it asks for it. The object is
// written as a hierarchical name because that is what an author names an
// object of a sealed design by, and the access holds characters no keyword is
// spelled with, so a value read back is the one the directive wrote.
constexpr std::string_view kObject = "top.dut.mem";
constexpr std::string_view kAccess = "read-only";

// A second object of the same envelope, for the case describing two.
constexpr std::string_view kOtherObject = "top.dut.ctrl";

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

// ---------------------------------------------------------------------------
// The expression describes objects within the current protected envelope.
// ---------------------------------------------------------------------------

// A viewport inside an open decryption envelope describes an object of it, and
// the name comes back whole: §34.5.32.2 has the name specify an object
// contained within the envelope, and an object of a sealed design is named by
// the path that reaches it, so a reading keeping the last component alone
// would describe a different object from the one asked for.
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

}  // namespace
