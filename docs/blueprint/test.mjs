import assert from 'node:assert/strict';
import {mkdir} from 'node:fs/promises';
import {chromium} from 'playwright-core';

const browser = await chromium.launch({executablePath:process.env.CHROME_PATH || 'google-chrome'});
const url = new URL('../BLUEPRINT.html', import.meta.url).href;
try {
  for (const width of [1360, 390]) {
    const page = await browser.newPage({viewport:{width, height:880}, offline:true});
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(url + '#theorem-2');
    const theorem = page.locator('#theorem-2');
    assert.equal(await page.locator('.chapter:visible').getAttribute('id'), 'gaussian-width');
    await page.evaluate(() => document.fonts.ready);
    assert.ok(await theorem.locator('.statement .math.display svg use').count());
    assert.equal(await page.locator('.math').count(), await page.locator('mjx-assistive-mml').count());
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    await theorem.locator('.proof summary').click();
    assert.ok(await theorem.locator('.proof_content').isVisible());
    await theorem.locator('.lean-button').click();
    assert.ok(await page.getByRole('dialog').isVisible());
    assert.equal(await page.locator('#dialog-body a').filter({hasText:'GenericChaining.finite_gaussian_majorizing_measure'}).count() > 0, true);
    await page.keyboard.press('Escape');
    assert.ok(!await page.getByRole('dialog').isVisible());
    await page.locator('#hide-proofs').click();
    assert.ok(!await theorem.locator('.proof_content').isVisible());
    if (process.env.BLUEPRINT_SCREENSHOTS) {
      await mkdir(process.env.BLUEPRINT_SCREENSHOTS, {recursive:true});
      await page.screenshot({path:process.env.BLUEPRINT_SCREENSHOTS + '/' + width + '.png'});
    }
    if (width < 1024) await page.locator('#toc-toggle').click();
    await page.locator('#contents a[href="#dependencies"]').click();
    await page.locator('.graph-plot a[href="#constructing-nets"]').click();
    assert.ok(await theorem.locator('.proof_content').isVisible());
    await page.goto(url + '#overview');
    assert.equal(await page.locator('#theorem-index tbody tr').count(), 9);
    for (const result of await page.locator('.result').all()) {
      assert.ok((await result.locator('.statement').textContent()).trim());
      assert.ok(await result.locator('.proof_content p').count());
    }
    assert.deepEqual(errors, []);
    await page.close();
  }
} finally {
  await browser.close();
}
