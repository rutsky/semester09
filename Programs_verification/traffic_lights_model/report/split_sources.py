#!/usr/bin/env python

with open("data/mail.pml", 'r') as f:
    contents = f.read()

contents.split("\n/*** cut here ***/\n")
