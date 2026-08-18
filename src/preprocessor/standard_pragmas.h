#ifndef DELTA_PREPROCESSOR_STANDARD_PRAGMAS_H
#define DELTA_PREPROCESSOR_STANDARD_PRAGMAS_H

#include <string_view>
#include <vector>

namespace delta {

// §22.11.1 "Standard pragmas": the pragma_names this standard defines, as
// against the implementation-specific specifications §22.11 leaves to the
// tool. The reset and resetall pragmas restore the default values and state of
// the pragma_keywords belonging to the pragmas they affect, and those defaults
// are the values the tool holds before any SystemVerilog text has been
// processed. reset restores the state of every pragma_name written as one of
// its own pragma_keywords; resetall restores the state of every pragma_name
// the implementation recognises.
inline constexpr std::string_view kResetPragmaName = "reset";
inline constexpr std::string_view kResetallPragmaName = "resetall";

// §22.11.1: every pragma_name this implementation recognises, which is what
// `pragma resetall restores. A pragma_name outside this set carries no state to
// restore, since §22.11 leaves the interpretation of the source text alone for
// a pragma_name the implementation does not recognise.
const std::vector<std::string_view>& RecognizedPragmaNames();

// §22.11.1: whether `name` names a pragma whose state a reset restores. This is
// what a pragma_keyword written on a `pragma reset directive is judged against,
// so a keyword naming anything else selects nothing to restore.
bool IsRecognizedPragmaName(std::string_view name);

}  // namespace delta

#endif  // DELTA_PREPROCESSOR_STANDARD_PRAGMAS_H
