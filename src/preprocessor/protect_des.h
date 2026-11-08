#pragma once

#include <cstddef>
#include <string>
#include <string_view>

namespace delta {

inline constexpr size_t kDesBlockBytes = 8;
inline constexpr size_t kDesKeyBytes = 8;

std::string DesEncryptBlock(std::string_view block, std::string_view key);

std::string DesDecryptBlock(std::string_view block, std::string_view key);

std::string DesCbcEncrypt(std::string_view cleartext, std::string_view key,
                          std::string_view iv);

bool DesCbcDecrypt(std::string_view ciphertext, std::string_view key,
                   std::string_view iv, std::string* cleartext);

}  // namespace delta
