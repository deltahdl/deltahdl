#pragma once

#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <utility>

namespace delta {

inline constexpr std::string_view kEncodingKeyword = "encoding";

inline constexpr std::string_view kEnctypeSubkeyword = "enctype";
inline constexpr std::string_view kLineLengthSubkeyword = "line_length";
inline constexpr std::string_view kBytesSubkeyword = "bytes";

inline constexpr std::string_view kUuencodeEnctype = "uuencode";
inline constexpr std::string_view kBase64Enctype = "base64";
inline constexpr std::string_view kQuotedPrintableEnctype = "quoted-printable";
inline constexpr std::string_view kRawEnctype = "raw";

inline constexpr std::string_view kBlockEnctype = "x-deltahdl-block";

struct ProtectEncodingAlgorithm {
  std::string_view enctype;
  bool required;
  std::string_view algorithm;
};

std::span<const ProtectEncodingAlgorithm> ProtectEncodingAlgorithms();

bool IsProtectEncodingAlgorithm(std::string_view enctype);

bool IsRequiredProtectEncodingAlgorithm(std::string_view enctype);

bool ProtectEncodingFitsOneLine(std::string_view enctype);

bool ProtectEncodingIsAvailable(std::string_view enctype);

struct ProtectEncoding {
  std::string enctype;
  size_t line_length = 0;
  size_t bytes = 0;
  bool has_bytes = false;
};

ProtectEncoding DefaultProtectEncoding();

struct ProtectEnvelopeEncodings {
  ProtectEnvelopeEncodings(const ProtectEncoding& both)
      : blocks(both), one_line(both) {}
  ProtectEnvelopeEncodings(ProtectEncoding block_scheme,
                           ProtectEncoding one_line_scheme)
      : blocks(std::move(block_scheme)), one_line(std::move(one_line_scheme)) {}

  ProtectEncoding blocks;
  ProtectEncoding one_line;
};

ProtectEncoding ParseProtectEncoding(std::string_view value);

std::string ProtectEncodingValue(const ProtectEncoding& encoding);

std::string ProtectEncodingDirective(const ProtectEncoding& encoding);

std::string ProtectEncodedValueDirective(const ProtectEncoding& encoding,
                                         size_t bytes);

std::string EncodeProtectBlock(std::string_view bytes,
                               const ProtectEncoding& encoding);

std::string EncodeProtectValue(std::string_view bytes,
                               const ProtectEncoding& encoding);

bool DecodeProtectBlock(std::string_view text, std::string_view enctype,
                        std::string* bytes);

enum class ProtectEncodedValueRead : uint8_t {
  kRead,
  kSchemeUnavailable,
  kNotWrittenInScheme,
};

ProtectEncodedValueRead ReadProtectEncodedValue(std::string_view text,
                                                const ProtectEncoding& encoding,
                                                std::string* bytes);

bool ProtectEncodedValueHasStatedSize(const ProtectEncoding& encoding,
                                      size_t bytes);

}  // namespace delta
