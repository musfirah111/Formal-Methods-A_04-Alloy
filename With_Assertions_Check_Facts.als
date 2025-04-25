
one sig NationalHolidays {
  dates: set String
}
abstract sig CaseStatus {}
one sig Open, Closed extends CaseStatus {}

abstract sig Person {
  id: one String,
  name: one String,
  email: one String,
  phoneNumber: one Int,
  dob: one String,
  gender: one String
}

sig Patient extends Person {
  prescription: some Prescription,
  appointment: some Appointment,
  bill: some Bill,
  ehr: one EHR,
  dischargeSummary: lone DischargeSummary,
  bed: lone Bed,
  caseStatus: one CaseStatus
}

sig Staff extends Person {
  type: one String,
  isOnLeave: one Int,
  qualification: some String,
  assignedShifts: set Shift
}

sig Doctor extends Staff {
  maxAppointmentsPerDay: one Int,
  rank: one String,
  appointments: set Appointment
}

sig Appointment {
  id: one String,
  type: one String,
  date: one String,
  status: one String,
  doctor: one Doctor,
  patient: one Patient,
  resources: some Resource,
  labTests: some LabTest,
  remainder: lone Remainder,
  timeSlot: one TimeSlot
}

sig Prescription {
  id: one String,
  medicines: some Medicine,
  appointment: one Appointment
}

sig Bill {
  totalAmount: one Int,
  isPaid: one Int,
  appointment: one Appointment
}

sig LabTest {
  id: one Int,
  appointment: one Appointment,
  testCost: one Int
}

sig EHR {
  id: one Int,
  dateCreated: one String,
  currentMedications: set Medicine,
  pastSurgeries: set Surgery,
  labTests: set LabTest,
  allergies: set Allergy,
  patient: one Patient,
  receivedtreatment: one Int
}

sig Bed {
  id: one Int,
  location: one String,
  isOccupied: one Int,
  assignedPatient: lone Patient,
  type: one String //"General Ward", "ICU", "CCU"
}

sig Surgery {
  id: one Int,
  anesthetist: one Staff,
  assignedOT: one String,
  appointment: one Appointment
}

sig DischargeSummary {
  summaryID: one Int,
  dischargeDate: one String,
  status: one String,
  signedBy: one Doctor,
  patient: one Patient
}

sig Pharmacy {
  medicines: some Medicine
}

sig Medicine {
  id: one String,
  name: one String,
  stock: one Int,
  threshold: one Int,
  allergens: set String,
  medicineCost: one Int
}

sig Allergy {
  allergyID: one String,
  name: one String,
  severity: one String,
  reaction: lone String,
  isClinicallyConfirmed: one Int,
  identificationDate: lone String
}

sig Resource {
  type: one String,
  isAvailable: one Int,
  resourceCost: one Int,
  appointment: one Appointment
}

sig Shift {
  id: one Int,
  date: one String,
  type: one String,  //Doctor, Nurse, QualityAssuranceTeam
  location: one String, 
  startingTime: one Time,
  endingTime: one Time,
  timeSlot: set TimeSlot,
  assignedTo: set Staff
}

sig TimeSlot {
  startingTime: one Time,
  endingTime: one Time
}

// Time.
sig Time {
  hour: one Int,
  minute: one Int
}

sig OperationTheater {
  id: one Int
}

sig Remainder {
  id: one Int,
  sentTime: one Time,
  remainderOfAppointment: one Appointment
}


sig Feedback {
  id: one Int,
  rating: one Int,
  comment: lone String,
  appointment: one Appointment,
  notifiedTeam: set Staff // Relation to staff of type "QualityAssuranceTeam"
}

sig LowStockAlert {
  medicine: one Medicine,
  generatedOn: one String,
  sentTo: one Staff
}


fun timeInMinutes[t: Time]: Int {
  mul[t.hour, 60] + t.minute
}


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Simple Structural>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. A doctor can be assigned to multiple patients.
fact DoctorCanHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

// Assertion
assert DoctorCanHaveMultiplePatientsAssertion {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}
check DoctorCanHaveMultiplePatientsAssertion for 5

//2. A resource can be assigned to only one patient at a time.
fact EachResourceAssignedToOnePatient {
  all r: Resource |
    one r.appointment.patient
}

// Assertion to ensure no two resources are assigned to the same patient at the same time.
assert ResourceAssignedToOnePatientAssertion {
  all r: Resource |
    one r.appointment.patient
}

check ResourceAssignedToOnePatientAssertion for 5

// 3. Each appointment is linked to one doctor and one patient.
fact EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}

// Assertion.
assert EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}
check EachAppointmentLinkedToDoctorAndPatient for 5

// 4. Each prescription is issued by a registered doctor.
fact PrescriptionsAreIssuedByDoctors {
  all p: Prescription |
    one p.appointment.doctor
}

// Assertion.
assert PrescriptionsAreIssuedByDoctorsAssertion {
  all p: Prescription |
    one p.appointment.doctor
}
check PrescriptionsAreIssuedByDoctorsAssertion for 5

// 5. Every bill corresponds to a single patient.
fact BillLinkedToOnePatient {
  all b: Bill | one b.appointment.patient
}

// Assertion.
assert BillLinkedToOnePatientAssertion {
  all b: Bill |
    one b.appointment.patient
}
check BillLinkedToOnePatientAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Moderate Logic Rules>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//1. Appointments are only allowed if a doctor is available.
fact AppointmentAllowedOnlyIfDoctorAvailable {
  all a: Appointment |
    some s: a.doctor.assignedShifts | s.date = a.date
}

// Assertion for AppointmentAllowedOnlyIfDoctorAvailable
assert AppointmentAllowedOnlyIfDoctorAvailableAssertion {
  all a: Appointment |
    some s: a.doctor.assignedShifts | s.date = a.date
}
check AppointmentAllowedOnlyIfDoctorAvailableAssertion for 5

//2. If a patient cancels an appointment, the time slot should become available again.
fact CancelledAppointmentFreesTimeSlot {
  all ts: TimeSlot |
    some a: Appointment | a.status = "cancelled" and a.timeSlot = ts =>
      all a2: Appointment | a2.timeSlot = ts implies a2.status = "cancelled"
}

// Assertion for CancelledAppointmentFreesTimeSlot
assert CancelledAppointmentFreesTimeSlotAssertion {
  all ts: TimeSlot |
    some a: Appointment | a.status = "cancelled" and a.timeSlot = ts =>
      all a2: Appointment | a2.timeSlot = ts implies a2.status = "cancelled"
}
check CancelledAppointmentFreesTimeSlotAssertion for 5

//3. If the medicine stock is less than the minimum threshold, notify the pharmacy admin.
fact GenerateAlertWhenStockLow {
  all m: Medicine |
    m.stock < m.threshold =>
      some a: LowStockAlert |
        a.medicine = m and
        some s: Staff |
          s.type = "PharmacyAdmin" and
          a.sentTo = s
}

// Assertion for GenerateAlertWhenStockLow
assert GenerateAlertWhenStockLowAssertion {
  all m: Medicine |
    m.stock < m.threshold =>
      some a: LowStockAlert |
        a.medicine = m and
        some s: Staff |
          s.type = "PharmacyAdmin" and
          a.sentTo = s
}
check GenerateAlertWhenStockLowAssertion for 5


//4. If a staff member is marked on leave, they cannot be assigned to duties that day.
fact StaffOnLeaveNotAssignedToShifts {
  all s: Staff |
    s.isOnLeave = 1 =>
      all sh: Shift |
        sh in s.assignedShifts implies no sh
}

// Assertion for StaffOnLeaveNotAssignedToShifts
assert StaffOnLeaveNotAssignedToShiftsAssertion {
  all s: Staff |
    s.isOnLeave = 1 =>
      all sh: Shift |
        sh in s.assignedShifts implies no sh
}
check StaffOnLeaveNotAssignedToShiftsAssertion for 5

//5. If the doctor has more than 25 patients in a day, no further appointments can be scheduled.
fact PerDayMax25PatientsPerDoctor {
  all d: Doctor, day: String |
    #({ a: Appointment | a.doctor = d and a.date = day }.patient) <= 25
}

// Assertion for PerDayMax25PatientsPerDoctor
assert PerDayMax25PatientsPerDoctorAssertion {
  all d: Doctor, day: String |
    #({ a: Appointment | a.doctor = d and a.date = day }.patient) <= 25
}
check PerDayMax25PatientsPerDoctorAssertion for 5

//6. Feedback can only be submitted after the appointment status is “Completed.”
fact FeedbackOnlyAfterCompletedAppointment {
  all f: Feedback |
    f.appointment.status = "Completed"
}

// Assertion for FeedbackOnlyAfterCompletedAppointment
assert FeedbackOnlyAfterCompletedAppointmentAssertion {
  all f: Feedback |
    f.appointment.status = "Completed"
}
check FeedbackOnlyAfterCompletedAppointmentAssertion for 5

//7. Appointment reminders must be sent 24 hours before the scheduled time.
fact remainderForAppointment {
  all a: Appointment | 
    some a.remainder => {
      let r = a.remainder,
          apptTime = a.timeSlot.startingTime,
          sentTime = r.sentTime |
        apptTime.hour - sentTime.hour = 24 and
        apptTime.minute = sentTime.minute
    }
}

// Assertion for remainderForAppointment
assert remainderForAppointmentAssertion {
  all a: Appointment | 
    some a.remainder => {
      let r = a.remainder,
          apptTime = a.timeSlot.startingTime,
          sentTime = r.sentTime |
        apptTime.hour - sentTime.hour = 24 and
        apptTime.minute = sentTime.minute
    }
}
check remainderForAppointmentAssertion for 5

//8. If a patient receives any treatment, then a billing entry must be automatically generated for the services used.
fact automaticBillGeneration {
  all p: Patient |
    all a: p.appointment |
      one e: EHR | e.patient = p and e.receivedtreatment = 1 implies
        some b: Bill | b.appointment = a
}

// Assertion for automaticBillGeneration
assert automaticBillGenerationAssertion {
  all p: Patient |
    all a: p.appointment |
      one e: EHR | e.patient = p and e.receivedtreatment = 1 implies
        some b: Bill | b.appointment = a
}
check automaticBillGenerationAssertion for 5

//9. Discharge summary must be uploaded before closing a patient case file.
fact DischargeSummaryBeforeCaseClosure {
  all p: Patient |
    p.caseStatus = Closed implies p.dischargeSummary != none and p.dischargeSummary.patient = p
}

// Assertion for DischargeSummaryBeforeCaseClosure
assert DischargeSummaryBeforeCaseClosureAssertion {
  all p: Patient |
    p.caseStatus = Closed implies p.dischargeSummary != none and p.dischargeSummary.patient = p
}
check DischargeSummaryBeforeCaseClosureAssertion for 5

//10. If a patient is assigned to the ICU, the system must auto-assign a nurse.
fact AutoAssignedNurseToICUPatient {
  all p: Patient |
    p.bed.isOccupied = 1 and p.bed.location = "ICU" implies
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
}

// Assertion for AutoAssignedNurseToICUPatient
assert AutoAssignedNurseToICUPatientAssertion {
  all p: Patient |
    p.bed.isOccupied = 1 and p.bed.location = "ICU" implies
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
}
check AutoAssignedNurseToICUPatientAssertion for 5


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Business or Real World Rules (5 - 10)>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//1. Appointments cannot be scheduled on national holidays except in emergencies.
fact NoAppointmentOnNationalHolidaysExceptEmergency{
   all a: Appointment | a.date in NationalHolidays.dates implies a.type = "Emergency"
}

// Assertion.
assert NoAppointmentOnNationalHolidaysExceptEmergencyAssertion {
  all a: Appointment |
    a.date in NationalHolidays.dates implies a.type = "Emergency"
}
check NoAppointmentOnNationalHolidaysExceptEmergencyAssertion for 5

//2. ICU patients must have 24/7 nursing.
fact ICUPatientsHaveNursing24_7{
  all p: Patient |
    p.bed != none and p.bed.type = "ICU" implies
      some s1, s2, s3: Shift, n1, n2, n3: Staff |
        n1.type = "Nurse" and n1 in s1.assignedTo and
        n2.type = "Nurse" and n2 in s2.assignedTo and
        n3.type = "Nurse" and n3 in s3.assignedTo
}

assert ICUPatientsHaveNursing24_7Assertion {
  all p: Patient |
    p.bed != none and p.bed.type = "ICU" implies
      some s1, s2, s3: Shift, n1, n2, n3: Staff |
        n1.type = "Nurse" and n1 in s1.assignedTo and
        n2.type = "Nurse" and n2 in s2.assignedTo and
        n3.type = "Nurse" and n3 in s3.assignedTo
}

check ICUPatientsHaveNursing24_7Assertion for 5

// 3. A discharge summary must be reviewed and signed by a senior doctor.
fact DischargeSummaryReviewdAndSignedBySeniorDoctor {
  all ds: DischargeSummary |
    ds.signedBy.rank = "Senior"
}

// Assertion to verify that all discharge summaries are signed by senior doctors
assert DischargeSummarySignedBySeniorDoctorAssertion {
  all ds: DischargeSummary |
    ds.signedBy.rank = "Senior"
}
check DischargeSummarySignedBySeniorDoctorAssertion for 5

//4. Emergency appointments override schedules.
fact EmergencyAppointmentsOverRideScdedules {
  all a1, a2: Appointment |
    a1 != a2 and 
    a1.date = a2.date and 
    a1.timeSlot = a2.timeSlot and 
    a1.doctor = a2.doctor and
    a1.type != "Emergency" and
    a2.type != "Emergency" =>
      a1.status = "Cancelled" or a2.status = "Cancelled"
}

// Assertion for Emergency appointments overriding schedules
assert EmergencyAppointmentsOverRideScdedulesAssertion {
  all a1, a2: Appointment |
    a1 != a2 and 
    a1.date = a2.date and 
    a1.timeSlot = a2.timeSlot and 
    a1.doctor = a2.doctor and
    a1.type != "Emergency" and
    a2.type != "Emergency" =>
      a1.status = "Cancelled" or a2.status = "Cancelled"
}
check EmergencyAppointmentsOverRideScdedulesAssertion for 5


//5. Poor feedback triggers a review.
fact PoorFeedbackTriggersReview {
   all f: Feedback |
    f.rating < 3 => {
      some qa: Staff | qa.type = "QualityAssuranceTeam" and qa in f.notifiedTeam
    }
}

// Assertion for Poor feedback triggering review
assert PoorFeedbackTriggersReviewAssertion {
  all f: Feedback |
    f.rating < 3 => {
      some qa: Staff | qa.type = "QualityAssuranceTeam" and qa in f.notifiedTeam
    }
}
check PoorFeedbackTriggersReviewAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< Assertion to Verify >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. All patients must have at least one EHR entry.
fact AtleastOneEHREntry {
  all p: Patient |
    some ehr: EHR | ehr.patient = p
}

// Assertion for AtleastOneEHREntry
assert AtleastOneEHREntryAssertion {
  all p: Patient |
    some ehr: EHR | ehr.patient = p
}
check AtleastOneEHREntryAssertion for 5

// All bills must match the sum of resources, lab tests, and medication costs.
fact BillMatchTheSum {
  all b: Bill | 
    let a = b.appointment |
    let total_Resources_Cost = sum r: a.resources | r.resourceCost |
    let total_LabTests_Cost = sum l: a.labTests | l.testCost |
    let total_Medicines_Cost = sum m: { m: Medicine | some pr: b.appointment.patient.prescription 
      | pr.appointment = a and m in pr.medicines } | m.medicineCost |
    b.totalAmount = total_Resources_Cost + total_LabTests_Cost + total_Medicines_Cost
}

// Assertion for BillMatchTheSum
assert BillMatchTheSumAssertion {
  all b: Bill | 
    let a = b.appointment |
    let total_Resources_Cost = sum r: a.resources | r.resourceCost |
    let total_LabTests_Cost = sum l: a.labTests | l.testCost |
    let total_Medicines_Cost = sum m: { m: Medicine | some pr: b.appointment.patient.prescription 
      | pr.appointment = a and m in pr.medicines } | m.medicineCost |
    b.totalAmount = total_Resources_Cost + total_LabTests_Cost + total_Medicines_Cost
}
check BillMatchTheSumAssertion for 5

// Meds can’t be issued without a prescription.
fact MedsCannotBeIssuedWithoutPrescription {
  all m: Medicine |
    some p: Prescription | p.medicines = m => some p
}

// Assertion for MedsCannotBeIssuedWithoutPrescription
assert MedsCannotBeIssuedWithoutPrescriptionAssertion {
  all m: Medicine |
    some p: Prescription | p.medicines = m => some p
}
check MedsCannotBeIssuedWithoutPrescriptionAssertion for 5


// Feedback must be linked to completed appointments.
fact FeedbackLinkedToCompletedAppointments {
  all f: Feedback |
    f.appointment.status = "Completed" and f.appointment = f.appointment
}

// Assertion for FeedbackLinkedToCompletedAppointments
assert FeedbackLinkedToCompletedAppointmentsAssertion {
  all f: Feedback |
    f.appointment.status = "Completed" and f.appointment = f.appointment
}
check FeedbackLinkedToCompletedAppointmentsAssertion for 5

// A resource must be available before it can be booked.
fact ResourceAvailabilityBeforeBooking {
  all r: Resource |
    r.isAvailable = 1 => some a: Appointment | a.resources = r
}

// Assertion for ResourceAvailabilityBeforeBooking
assert ResourceAvailabilityBeforeBookingAssertion {
  all r: Resource |
    r.isAvailable = 1 => some a: Appointment | a.resources = r
}
check ResourceAvailabilityBeforeBookingAssertion for 5