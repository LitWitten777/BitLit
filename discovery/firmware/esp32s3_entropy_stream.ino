// ESP32-S3 entropy stream for the QBX discovery loop (Arduino core for ESP32, 2.x/3.x).
//
// UNTESTED ON HARDWARE: this sketch was written without access to a board.  Capture a dump
// first and health-test it on the host:
//   cat /dev/ttyACM0 | head -c 65536 > dump.bin
//   python3 -m discovery.engine entropy --entropy-device dump.bin --device-h 1.0
//
// It writes raw bytes to USB-CDC serial, with no framing:
//   MODE_RAW_ADC  : the low 8 bits of successive 12-bit ADC conversions of a floating pin
//                   (thermal / RF pickup).  These are RAW samples: they are what the host's
//                   SP 800-90B health tests are meant for.  Declare at most ~1 bit/byte
//                   (--device-h 1.0) unless an SP 800-90B entropy assessment says more.
//   MODE_HW_RNG   : esp_random() words.  The ESP32-S3 hardware RNG mixes RF/ADC noise only
//                   while Wi-Fi/Bluetooth is on or after bootloader_random_enable(); its output
//                   is already conditioned, so host health tests can only detect gross faults.
//
// Floating-pin ADC noise is easily dominated by deterministic interference (USB, switching
// regulators, mains hum); the host drops the source if the repetition-count or
// adaptive-proportion test fails, and the run then continues on os.urandom alone.

#include <Arduino.h>
#include "esp_random.h"
#include "bootloader_random.h"

#define MODE_RAW_ADC 1
#define MODE_HW_RNG  2
#ifndef ENTROPY_MODE
#define ENTROPY_MODE MODE_RAW_ADC
#endif

static const int kFloatingPin = 4;   // ADC1 channel on GPIO4; leave it unconnected
static uint8_t buf[256];

void setup() {
  Serial.begin(2000000);
  analogReadResolution(12);
#if ENTROPY_MODE == MODE_HW_RNG
  bootloader_random_enable();        // enables the RF/ADC noise source without Wi-Fi
#endif
}

void loop() {
#if ENTROPY_MODE == MODE_RAW_ADC
  for (size_t i = 0; i < sizeof(buf); ++i) {
    buf[i] = (uint8_t)(analogRead(kFloatingPin) & 0xFF);
  }
#else
  for (size_t i = 0; i < sizeof(buf); i += 4) {
    uint32_t w = esp_random();
    memcpy(buf + i, &w, 4);
  }
#endif
  Serial.write(buf, sizeof(buf));
}
