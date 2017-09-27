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

package com.horndroid.printers;

import com.horndroid.exceptions.ReportWritingException;
import com.horndroid.model.Report;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;

/**
 * This report writer interface can be used to generate JSON/XML/Custom files
 * with report content
 */
public abstract class ReportPrinter {

    protected abstract String getReportInString(Report report) throws ReportWritingException;

    public void writeReportToFile(Report report, String filename) throws ReportWritingException {
        String s = getReportInString(report);
        try {
            FileUtils.writeStringToFile(new File(filename), s);
        } catch (IOException e) {
            throw new ReportWritingException("Problem writing report to file", e);
        }
    }

    public void printReport(Report report) throws ReportWritingException {
        String s = getReportInString(report);
        System.out.println(s);
    }

}
