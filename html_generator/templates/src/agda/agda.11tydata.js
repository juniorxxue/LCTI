export default async function () {
  return {
    layout: "agda",
    templateEngineOverride: false,
    permalink: (data) => `${data.page.filePathStem}.html`
  }
}
