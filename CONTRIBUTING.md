# Contributing

Thank you for your help. This file tells how to send a change.

1. Read spec 07 of tamnd/mathlib. It gives the parts of a section, the Mathlib box and the voice.
2. Make a branch from `main`. Keep one subject in one pull request.
3. Give the pull request one `area/*` label, one `type/*` label and the milestone.
4. Run `python3 scripts/style.py`. It must print nothing.
5. A section and its Lean files in mathlib-lean merge together or not at all.

## The writing rules

The text follows ASD-STE100 technical English.

1. Write short sentences. Use one idea in one sentence.
2. Use the active voice. Do not use "we".
3. Do not use an em dash or an en dash. Use a comma, a colon or a new sentence.
4. Do not break a line in the middle of a sentence. Write each paragraph on one line.
5. Do not add a page break.
6. Write math in `$...$`.
7. Write a Lean name in backticks, exactly as Mathlib has it.

## Reports of errors

Open an issue with the label `type/fix`. Give the volume, the section, the edition and what is wrong. An error of mathematics gets a fix in the next patch release (spec 14.6 of tamnd/mathlib).
