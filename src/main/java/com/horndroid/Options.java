
/*
 * MIT License
 *
 * Copyright (c) 2017 TU Wien
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

package com.horndroid;

public class Options {
    public boolean arrays = false;
    public boolean debug = false;
    public boolean verboseResults = false;
    public String outputDirectory = "";
    public int apiLevel = 15;
    public int bitvectorSize = 64;
    public int maxQueries = 0;
    public int debugInt = 3;
    public boolean stubs = false;
    public int timeout = 30;
    public boolean tillFirstLeak = false;
    public boolean sensIfHasSink = false;
    public boolean oldUnknown = false;
    public boolean nfsanalysis = false;
    public boolean pointersMerge = false;
    public boolean nopUnknown = false;
    public int filterClasses = 0;
    public boolean filterClassesSound = false;
}