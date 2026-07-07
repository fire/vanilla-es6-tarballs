import { defineConfig } from "@playwright/test";

export default defineConfig({
  testDir: "./playwright",
  testMatch: /.*\.spec\.mjs/,
  use: { baseURL: "http://localhost:8765" },
  webServer: {
    command: "node scripts/serve.mjs",
    url: "http://localhost:8765/",
    reuseExistingServer: !process.env.CI,
  },
});
