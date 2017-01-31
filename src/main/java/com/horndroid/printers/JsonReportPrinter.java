package com.horndroid.printers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.horndroid.exceptions.ReportWritingException;
import com.horndroid.model.Report;

class JsonReportPrinter extends ReportPrinter {


    @Override
    protected String getReportInString(Report report) throws ReportWritingException {
        ObjectMapper mapper = new ObjectMapper();

        String json;
        try {
            json = mapper.writeValueAsString(report);
        } catch (JsonProcessingException e) {
            throw new ReportWritingException(e.getMessage());
        }
        return json;
    }
}
