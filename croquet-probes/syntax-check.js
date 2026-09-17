/* Parse a JavaScript file without running it, and say whether it is well formed.
   For the Croquet glue (primordialsoup/meta/croquet-post.js), which cannot be
   loaded outside a page.

     croquet-probes/run.sh syntax-check.js /abs/path/to/file.js [more.js ...] */
const fs = require('fs');
const vm = require('vm');
let bad = 0;
for (const f of process.argv.slice(2)) {
  try {
    new vm.Script(fs.readFileSync(f, 'utf8'), { filename: f });
    console.log('SYNTAX-OK  ' + f);
  } catch (e) {
    bad++;
    console.log('SYNTAX-ERROR  ' + f + '\n' + (e.stack || e));
  }
}
process.exitCode = bad ? 1 : 0;
