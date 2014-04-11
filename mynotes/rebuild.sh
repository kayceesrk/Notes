#!/bin/bash

jekyll build
ssh cmed rm -rf /p/sss/www/multiMLton/mML/Notes
scp -r _site/ cmed:/p/sss/www/multiMLton/mML/Notes
