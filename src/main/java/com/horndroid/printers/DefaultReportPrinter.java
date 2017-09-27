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

import com.horndroid.model.Report;
import com.horndroid.model.ReportEntry;

import java.util.List;


public final class DefaultReportPrinter extends ReportPrinter {


    protected String getReportInString(Report report) {
        int i = 1;
        String s = "";
        s += report.getTag() + " :\n";
        s += "Number of queries :" + report.getNumberOfQueries() + "\n";
        final List<ReportEntry> reportEntries = report.getReportEntries();
        for (ReportEntry reportEntry : reportEntries) {
            s += i + ": ";
            if (reportEntry.isVerbose())
                s += reportEntry.getDescription() + "\n";
            s += reportEntry.getResult() + "\n";
            i++;
        }
        return s;
    }


}
